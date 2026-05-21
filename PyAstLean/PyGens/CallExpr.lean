import Mathlib
import PyAstLean.Codegen
import PyAstLean.PyGens.Basic
import PyAstLean.PyGens.Attributes

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Local effect probe for early string-lowering code, before the general call helpers below. -/
partial def stringJsonUsesExceptionEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "except" => true
    | _ =>
        match json.getObjValAs? String "node_type" with
        | .ok nodeType => nodeType == "Try" || nodeType == "Raise"
        | .error _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any stringJsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => stringJsonUsesExceptionEffect value)
    | _ => false

/-- Local effect probe for `IO`-bearing string pieces such as `input()` inside f-strings. -/
partial def stringJsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any stringJsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => stringJsonUsesIOEffect value)
    | _ => false

/-- Detect whether an early string subtree contains any translated monadic effect. -/
def stringJsonUsesMonadicEffect (json : Json) : Bool :=
  stringJsonUsesExceptionEffect json || stringJsonUsesIOEffect json

@[pygen "FormattedValue"]
def formattedValueSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
    let valueCode ← getCode valueJson `term
    let toStringIdent := mkIdent ``toString
    if stringJsonUsesMonadicEffect valueJson then
      let binder := mkIdent `__py_fmt
      let stringIdent := mkIdent ``String
      let effectTy ←
        if stringJsonUsesExceptionEffect valueJson then
          let exceptIdent := mkIdent ``PyAstLean.PyExcept
          `($exceptIdent $stringIdent)
        else
          let ioIdent := mkIdent ``IO
          `($ioIdent $stringIdent)
      `(((do
            let $binder:ident ← $valueCode:term
            return ($toStringIdent $binder:term)) :
          $effectTy))
    else
      `($toStringIdent $valueCode)
  | _, _ => throwError s!"Unsupported syntax category for FormattedValue node"

@[pygen "JoinedStr"]
def joinedStrSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valuesJson := json.getObjValAs? Json "values" | throwError
      s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
    let valuesArray ← match valuesJson with
      | .arr arr => pure arr
      | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
    let valuesCodes ← valuesArray.mapM (fun valueJson => getCode valueJson `term)
    let appendIdent := mkIdent ``String.append
    let mut res : TSyntax `term ← `("")
    let mut bindings : Array (TSyntax `doElem) := #[]
    for idx in [0:valuesCodes.size] do
      let valueJson := valuesArray[idx]!
      let valueCode := valuesCodes[idx]!
      if stringJsonUsesMonadicEffect valueJson then
        let binder := mkIdent (s!"__py_join{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $valueCode:term))
        res ← `($appendIdent $res $binder:term)
      else
        res ← `($appendIdent $res $valueCode)
    if bindings.isEmpty then
      return res
    let stringIdent := mkIdent ``String
    let effectTy ←
      if stringJsonUsesExceptionEffect json then
        let exceptIdent := mkIdent ``PyAstLean.PyExcept
        `($exceptIdent $stringIdent)
      else
        let ioIdent := mkIdent ``IO
        `($ioIdent $stringIdent)
    `(((do
          $[$bindings:doElem]*
          return $res:term) :
        $effectTy))
  | _, _ => throwError s!"Unsupported syntax category for JoinedStr node"

/-- Local copy of the exception-effect probe so `Call.doElem` can avoid a cyclic import on `Utils`. -/
partial def basicJsonUsesExceptionEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "except" => true
    | _ =>
        match json.getObjValAs? String "node_type" with
        | .ok nodeType => nodeType == "Try" || nodeType == "Raise"
        | .error _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any basicJsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => basicJsonUsesExceptionEffect value)
    | _ => false

/-- Local copy of the IO-effect probe so `Call` can lift nested `input(...)` / `print(...)` expressions. -/
partial def basicJsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any basicJsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => basicJsonUsesIOEffect value)
    | _ => false

/-- Detect whether a JSON subtree contains any translated monadic effect. -/
def basicJsonUsesMonadicEffect (json : Json) : Bool :=
  basicJsonUsesExceptionEffect json || basicJsonUsesIOEffect json

/--
Inline simple translated `IO` expressions directly as terms that contain local `←` binds.

This is used in surrounding `do` notation so code like `b = int(input())` can become
`let mut b := PyAstLean.pyInt (← PyAstLean.pyInputIO "")` instead of an extra nested
`do ... : IO _` wrapper.
-/
partial def inlineIOTerm (json : Json) : PygenM (TSyntax `term) := do
  if !basicJsonUsesIOEffect json then
    return ← getCode json `term
  let some nodeType := json.getObjValAs? String "node_type" |>.toOption
    | return ← getCode json `term
  match nodeType with
  | "Call" =>
      let .ok funcJson := json.getObjValAs? Json "func" | throwError
        s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
      let .ok argsJson := json.getObjValAs? Json "args" | throwError
        s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
      let argsArray ← match argsJson with
        | .arr arr => pure arr
        | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
      let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
        s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
      let .ok keyWordsMap := keyWordsJson.getObj? | throwError
        s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok "input" => do
          unless keyWordsMap.isEmpty do
            throwError "input() keyword arguments are not supported yet."
          unless argsArray.size ≤ 1 do
            throwError "input() expects zero or one positional argument."
          let pyInputIOIdent := mkIdent ``pyInputIO
          match argsArray.size with
          | 0 => `((← $pyInputIOIdent ""))
          | 1 =>
              let arg0 ← inlineIOTerm argsArray[0]!
              `((← $pyInputIOIdent $arg0))
          | _ => throwError "input() expects zero or one positional argument."
      | .ok "Name", .ok "int" => do
          unless keyWordsMap.isEmpty do
            throwError "int() keyword arguments are not supported yet."
          unless argsArray.size == 1 do
            throwError "int() expects exactly one positional argument."
          let pyIntIdent := mkIdent ``pyInt
          let arg0 ← inlineIOTerm argsArray[0]!
          `($pyIntIdent $arg0)
      | _, _ =>
          let mut inlineArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              inlineArgs := inlineArgs.push (← inlineIOTerm argJson)
            else
              match argJson.getObjValAs? String "node_type", argJson.getObjValAs? String "id" with
              | .ok "Name", .ok funcName =>
                  let mappedName ← leanName funcName.toName
                  inlineArgs := inlineArgs.push ((mkIdent mappedName : TSyntax `term))
              | _, _ =>
                  inlineArgs := inlineArgs.push (← getCode argJson `term)
          let mut funcTerm : TSyntax `term ← `("")
          if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
            let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
              s!"Attribute node missing 'value' field: {funcJson}"
            let .ok attr := funcJson.getObjValAs? String "attr" | throwError
              s!"Attribute node missing 'attr' field: {funcJson}"
            let receiverTerm ←
              if basicJsonUsesIOEffect valueJson then
                inlineIOTerm valueJson
              else
                getCode valueJson `term
            match pythonMethodMap attr with
            | some funcName =>
                let mapped := mkIdent funcName
                funcTerm ← `($mapped $receiverTerm)
            | none =>
                let attrId := mkIdent attr.toName
                funcTerm ← `($receiverTerm.$attrId)
          else
            match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
            | .ok "Name", .ok funcName =>
                let mappedName ← leanName funcName.toName
                funcTerm := (mkIdent mappedName : TSyntax `term)
            | _, _ =>
                funcTerm ← getCode funcJson `term
          let mut t ← `($funcTerm $inlineArgs*)
          for (kwName, kwValueJson) in keyWordsMap.toList do
            let kwValueCode ←
              if basicJsonUsesIOEffect kwValueJson then
                inlineIOTerm kwValueJson
              else
                getCode kwValueJson `term
            let kwId := mkIdent kwName.toName
            t ← `($t ($kwId:ident := $kwValueCode))
          return t
  | "FormattedValue" => do
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
      let valueCode ← inlineIOTerm valueJson
      let toStringIdent := mkIdent ``toString
      `($toStringIdent $valueCode)
  | "JoinedStr" => do
      let .ok valuesJson := json.getObjValAs? Json "values" | throwError
        s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
      let valuesArray ← match valuesJson with
        | .arr arr => pure arr
        | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
      let appendIdent := mkIdent ``String.append
      let mut res : TSyntax `term ← `("")
      for valueJson in valuesArray do
        let valueCode ← inlineIOTerm valueJson
        res ← `($appendIdent $res $valueCode)
      pure res
  | _ =>
      return ← getCode json `term

/--
Hoist translated `IO` subexpressions into surrounding `do` blocks and return a pure term
that refers to the bound result.

This is the small ANF-style helper used to keep generated Lean readable for common cases
like `int(input())`, `print(input())`, and f-strings containing `input()`.
-/
partial def hoistIOTerm (json : Json) : PygenM (Array (TSyntax `doElem) × TSyntax `term) := do
  if !basicJsonUsesIOEffect json then
    return (#[], ← getCode json `term)
  let some nodeType := json.getObjValAs? String "node_type" |>.toOption
    | return (#[], ← getCode json `term)
  match nodeType with
  | "Call" =>
      let .ok funcJson := json.getObjValAs? Json "func" | throwError
        s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
      let .ok argsJson := json.getObjValAs? Json "args" | throwError
        s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
      let argsArray ← match argsJson with
        | .arr arr => pure arr
        | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
      let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
        s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
      let .ok keyWordsMap := keyWordsJson.getObj? | throwError
        s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok "input" => do
          unless keyWordsMap.isEmpty do
            throwError "input() keyword arguments are not supported yet."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          let pyInputIOIdent := mkIdent ``pyInputIO
          let action ← match resolvedArgs.size with
            | 0 => `($pyInputIOIdent "")
            | 1 =>
                let arg0 := resolvedArgs[0]!
                `($pyInputIOIdent $arg0)
            | _ => throwError "input() expects zero or one positional argument."
          let binder := mkIdent (s!"__py_input{bindings.size}").toName
          let finalBindings := bindings.push (← `(doElem| let $binder:ident ← $action:term))
          return (finalBindings, binder)
      | .ok "Name", .ok "int" => do
          unless keyWordsMap.isEmpty do
            throwError "int() keyword arguments are not supported yet."
          unless argsArray.size == 1 do
            throwError "int() expects exactly one positional argument."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          let pyIntIdent := mkIdent ``pyInt
          let arg0 := resolvedArgs[0]!
          return (bindings, ← `($pyIntIdent $arg0))
      | .ok "Name", .ok "print" => do
          let supportedKeywords := ["sep", "end"]
          for (kwName, _) in keyWordsMap.toList do
            unless supportedKeywords.contains kwName do
              throwError s!"print() keyword argument '{kwName}' is not supported yet."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          let pyPrintIOIdent := mkIdent ``pyPrintIO
          let action ← match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
            | none, none =>
                `($pyPrintIOIdent [$resolvedArgs,*])
            | _, _ =>
                let sepCode ← match keyWordsMap.get? "sep" with
                  | some sepJson => getCode sepJson `term
                  | none => `(" ")
                let endCode ← match keyWordsMap.get? "end" with
                  | some endJson => getCode endJson `term
                  | none => `("\n")
                `($pyPrintIOIdent [$resolvedArgs,*] $sepCode $endCode)
          let binder := mkIdent (s!"__py_print{bindings.size}").toName
          let finalBindings := bindings.push (← `(doElem| let $binder:ident ← $action:term))
          return (finalBindings, binder)
      | _, _ =>
          return (#[], ← getCode json `term)
  | "FormattedValue" => do
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
      let (bindings, valueTerm) ← hoistIOTerm valueJson
      let toStringIdent := mkIdent ``toString
      return (bindings, ← `($toStringIdent $valueTerm))
  | "JoinedStr" => do
      let .ok valuesJson := json.getObjValAs? Json "values" | throwError
        s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
      let valuesArray ← match valuesJson with
        | .arr arr => pure arr
        | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
      let appendIdent := mkIdent ``String.append
      let mut bindings : Array (TSyntax `doElem) := #[]
      let mut res : TSyntax `term ← `("")
      for valueJson in valuesArray do
        let (pieceBindings, pieceTerm) ← hoistIOTerm valueJson
        bindings := bindings ++ pieceBindings
        res ← `($appendIdent $res $pieceTerm)
      return (bindings, res)
  | _ =>
      return (#[], ← getCode json `term)

/--
Lift a pure function application into `IO` when any argument is already monadic.

This is the bridge that lets expressions like `int(input())` stay well-typed: we first
bind the `IO` arguments, then apply the pure function to the resolved values.
-/
def buildIOPureApplicationFromArgs (argJsons : Array Json) (argCodes : Array (TSyntax `term))
    (mkResult : Array (TSyntax `term) → PygenM (TSyntax `term)) : PygenM (TSyntax `term) := do
  let mut bindings : Array (TSyntax `doElem) := #[]
  let mut resolvedArgs : Array (TSyntax `term) := #[]
  for idx in [0:argCodes.size] do
    let argJson := argJsons[idx]!
    let argCode := argCodes[idx]!
    if basicJsonUsesIOEffect argJson then
      let (argBindings, argTerm) ← hoistIOTerm argJson
      if argBindings.isEmpty then
        let binder := mkIdent (s!"__py_arg{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $argTerm:term))
        resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
      else
        bindings := bindings ++ argBindings
        resolvedArgs := resolvedArgs.push argTerm
    else if basicJsonUsesMonadicEffect argJson then
      let binder := mkIdent (s!"__py_arg{idx}").toName
      bindings := bindings.push (← `(doElem| let $binder:ident ← $argCode:term))
      resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
    else
      resolvedArgs := resolvedArgs.push argCode
  let resultTerm ← mkResult resolvedArgs
  if bindings.isEmpty then
    return resultTerm
  let ioIdent := mkIdent ``IO
  `(((do
        $[$bindings:doElem]*
        return $resultTerm:term) : $ioIdent _))

/--
Lift an `IO`-returning application when some arguments are already monadic.

This keeps expressions like `print(input())` and prompted `input(...)` well-typed by
binding the monadic arguments before running the final `IO` action.
-/
def buildIOActionApplicationFromArgs (argJsons : Array Json) (argCodes : Array (TSyntax `term))
    (mkAction : Array (TSyntax `term) → PygenM (TSyntax `term)) : PygenM (TSyntax `term) := do
  let mut bindings : Array (TSyntax `doElem) := #[]
  let mut resolvedArgs : Array (TSyntax `term) := #[]
  for idx in [0:argCodes.size] do
    let argJson := argJsons[idx]!
    let argCode := argCodes[idx]!
    if basicJsonUsesIOEffect argJson then
      let (argBindings, argTerm) ← hoistIOTerm argJson
      if argBindings.isEmpty then
        let binder := mkIdent (s!"__py_arg{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $argTerm:term))
        resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
      else
        bindings := bindings ++ argBindings
        resolvedArgs := resolvedArgs.push argTerm
    else if basicJsonUsesMonadicEffect argJson then
      let binder := mkIdent (s!"__py_arg{idx}").toName
      bindings := bindings.push (← `(doElem| let $binder:ident ← $argCode:term))
      resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
    else
      resolvedArgs := resolvedArgs.push argCode
  let actionTerm ← mkAction resolvedArgs
  if bindings.isEmpty then
    return actionTerm
  let ioIdent := mkIdent ``IO
  `(((do
        $[$bindings:doElem]*
        let __py_result ← $actionTerm:term
        return __py_result) : $ioIdent _))

/-- Infer a simple runtime type from a value expression when the shape is obvious. -/
def inferSimpleValueTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match json.getObjValAs? String "node_type" with
  | .ok "Constant" =>
      let .ok value := json.getObjValAs? Json "value" | throwError
        s!"Constant node does not have a 'value' field or it is not a JSON value: {json}"
      match value with
      | .num (JsonNumber.mk _ exponent) =>
          if exponent == 0 then
            return some (mkIdent ``Int)
          else
            return some (mkIdent ``Rat)
      | .str _ => return some (mkIdent ``String)
      | .bool _ => return some (mkIdent ``Bool)
      | _ => return none
  | _ => return none

/-- Infer a simple iterable element type from obvious literal iterables. -/
def inferIterableElemTypeSyntax? (json : Json) : PygenM (Option (TSyntax `term)) := do
  match json.getObjValAs? String "node_type" with
  | .ok "List" => do
      let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
        s!"List node does not have an 'elts' field or it is not a JSON value: {json}"
      match eltsJson with
      | .arr arr =>
          match arr[0]? with
          | some first => inferSimpleValueTypeSyntax? first
          | none => return none
      | _ => return none
  | .ok "Tuple" => do
      let .ok eltsJson := json.getObjValAs? Json "elts" | throwError
        s!"Tuple node does not have an 'elts' field or it is not a JSON value: {json}"
      match eltsJson with
      | .arr arr =>
          match arr[0]? with
          | some first => inferSimpleValueTypeSyntax? first
          | none => return none
      | _ => return none
  | .ok "Constant" => do
      let .ok value := json.getObjValAs? Json "value" | throwError
        s!"Constant node does not have a 'value' field or it is not a JSON value: {json}"
      match value with
      | .str _ => return some (mkIdent ``Char)
      | _ => return none
  | _ => return none

/-- Read the positional parameter names from a lambda node without depending on `FuncDef.lean`. -/
def lambdaArgIdents (json : Json) : PygenM (Array (TSyntax `ident)) := do
  let .ok argsJson := json.getObjValAs? Json "args" | throwError
    s!"Lambda node does not have an 'args' field or it is not a JSON value: {json}"
  let .ok argsArray := argsJson.getObjValAs? (Array Json) "args" | throwError
    s!"Lambda args does not have an 'args' field or it is not a JSON array: {argsJson}"
  argsArray.mapM fun argJson => do
    let .ok argName := argJson.getObjValAs? String "arg" | throwError
      s!"Lambda argument does not have an 'arg' field or it is not a string: {argJson}"
    pure (mkIdent argName.toName)

/--
If a `reduce` combiner is a two-argument lambda, stamp both lambda parameters with either
a concrete runtime type or `_` placeholders so overloaded arithmetic does not drift too
early during elaboration.
-/
def typedReduceLambdaCode (funcJson : Json) (fallback : TSyntax `term)
    (paramTy? : Option (TSyntax `term)) : PygenM (TSyntax `term) := do
  unless funcJson.getObjValAs? String "node_type" == .ok "Lambda" do
    return fallback
  let argIdents ← lambdaArgIdents funcJson
  unless argIdents.size == 2 do
    return fallback
  let .ok bodyJson := funcJson.getObjValAs? Json "body" | throwError
    s!"Lambda node does not have a 'body' field or it is not a JSON value: {funcJson}"
  let bodyStx ← getCode bodyJson `term
  let arg0 := argIdents[0]!
  let arg1 := argIdents[1]!
  let paramTy ← match paramTy? with
    | some stx => pure stx
    | none => `(_)
  `(fun ($arg0 : $paramTy) ↦ fun ($arg1 : $paramTy) ↦ $bodyStx)

/-- Map a bare Python builtin function name to the Lean runtime symbol when it is used as a value. -/
def mappedCallableValueCode (json : Json) : PygenM (TSyntax `term) := do
  match ← jsonLibraryMappedName? json with
  | some leanName =>
      pure (mkIdent leanName : TSyntax `term)
  | none =>
      match json.getObjValAs? String "node_type", json.getObjValAs? String "id" with
      | .ok "Name", .ok funcName =>
          let mappedName ← leanName funcName.toName
          pure (mkIdent mappedName : TSyntax `term)
      | _, _ =>
          getCode json `term

@[pygen "Call"]
def callSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
    let argsArray ← match argsJson with
      | .arr arr => pure arr
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
    let argsCodes ← argsArray.mapM (fun argJson => getCode argJson `term)

    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"

    let mut allArgs : Array (TSyntax `term) := #[]
    let mut allArgJsons : Array Json := #[]
    let mut funcIdent : TSyntax `term ← `("")

    match ← jsonLibraryMappedName? funcJson with
    | some leanName =>
        funcIdent := (mkIdent leanName : TSyntax `term)
    | none =>
      if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
        let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
          s!"Attribute node missing 'value' field: {funcJson}"
        let .ok attr := funcJson.getObjValAs? String "attr" | throwError
          s!"Attribute node missing 'attr' field: {funcJson}"

        if attr == "reduce" && valueJson.getObjValAs? String "node_type" == .ok "Name" &&
            valueJson.getObjValAs? String "id" == .ok "functools" then
          unless keyWordsMap.isEmpty do
            throwError "functools.reduce() keyword arguments are not supported yet."
          match argsArray.size with
          | 2 =>
              let pyReduceNoInitIdent := mkIdent ``pyReduceNoInit
              let elemTy? ← inferIterableElemTypeSyntax? argsArray[1]!
              let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! elemTy?
              let adjustedCodes := #[funcCode, argsCodes[1]!]
              return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                let f := resolvedArgs[0]!
                let xs := resolvedArgs[1]!
                `($pyReduceNoInitIdent $xs $f)
          | 3 =>
              let pyReduceIdent := mkIdent ``pyReduce
              let initTy? ← inferSimpleValueTypeSyntax? argsArray[2]!
              let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! initTy?
              let adjustedCodes := #[funcCode, argsCodes[1]!, argsCodes[2]!]
              return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                let f := resolvedArgs[0]!
                let xs := resolvedArgs[1]!
                let init := resolvedArgs[2]!
                `($pyReduceIdent $xs $f $init)
          | _ =>
              throwError "functools.reduce() expects two or three positional arguments."

        if attr == "get" then
          unless keyWordsMap.isEmpty do
            throwError "get() calls with keyword arguments are not supported yet."
          let valCode ← getCode valueJson `term
          match argsArray.size with
          | 1 =>
              let keyCode ← getCode argsArray[0]! `term
              let pyGetOptIdent := mkIdent ``pyGetOpt
              return ← `($pyGetOptIdent $valCode $keyCode)
          | 2 =>
              let keyCode ← getCode argsArray[0]! `term
              let defaultCode ← getCode argsArray[1]! `term
              let pyGetDIdent := mkIdent ``pyGetD
              return ← `($pyGetDIdent $valCode $keyCode $defaultCode)
          | _ =>
              throwError "get() expects one or two positional arguments."

        if attr == "sort" then
          throwError "sort() is only supported as a statement; use sorted(x) in expressions."

        let valCode ← getCode valueJson `term
        allArgs := allArgs.push valCode
        allArgJsons := allArgJsons.push valueJson

        match pythonMethodMap attr with
        | some funcName =>
            funcIdent := mkIdent funcName
        | none =>
            throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            return ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let pyPrintIOIdent := mkIdent ``pyPrintIO
              match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
              | none, none =>
                  `($pyPrintIOIdent [$resolvedArgs,*])
              | _, _ =>
                  let sepCode ← match keyWordsMap.get? "sep" with
                    | some sepJson => getCode sepJson `term
                    | none => `(" ")
                  let endCode ← match keyWordsMap.get? "end" with
                    | some endJson => getCode endJson `term
                    | none => `("\n")
                  `($pyPrintIOIdent [$resolvedArgs,*] $sepCode $endCode)
        | .ok "Name", .ok "input" => do
            unless keyWordsMap.isEmpty do
              throwError "input() keyword arguments are not supported yet."
            unless argsArray.size ≤ 1 do
              throwError "input() expects zero or one positional argument."
            let pyInputIOIdent := mkIdent ``pyInputIO
            return ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              match resolvedArgs.size with
              | 0 => `($pyInputIOIdent "")
              | 1 =>
                  let arg0 := resolvedArgs[0]!
                  `($pyInputIOIdent $arg0)
              | _ => throwError "input() expects zero or one positional argument."
        | .ok "Name", .ok "int" => do
            unless keyWordsMap.isEmpty do
              throwError "int() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "int() expects exactly one positional argument."
            let pyIntIdent := mkIdent ``pyInt
            return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyIntIdent $arg0)
        | .ok "Name", .ok "str" => do
            unless keyWordsMap.isEmpty do
              throwError "str() keyword arguments are not supported yet."
            return ← match argsArray.size with
            | 0 => `("")
            | 1 =>
                let pyStrIdent := mkIdent ``pyStr
                buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                  let arg0 := resolvedArgs[0]!
                  `($pyStrIdent $arg0)
            | _ =>
                throwError "str() expects zero or one positional argument."
        | .ok "Name", .ok "list" => do
            unless keyWordsMap.isEmpty do
              throwError "list() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "list() currently expects exactly one positional argument."
            let pyListIdent := mkIdent ``pyList
            return ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyListIdent $arg0)
        | .ok "Name", .ok "map" => do
            unless keyWordsMap.isEmpty do
              throwError "map() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "map() currently expects exactly two positional arguments."
            let pyMapIdent := mkIdent ``pyMap
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyMapIdent $f $xs)
        | .ok "Name", .ok "filter" => do
            unless keyWordsMap.isEmpty do
              throwError "filter() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "filter() currently expects exactly two positional arguments."
            let pyFilterIdent := mkIdent ``pyFilter
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyFilterIdent $f $xs)
        | .ok "Name", .ok "reduce" => do
            unless keyWordsMap.isEmpty do
              throwError "reduce() keyword arguments are not supported yet."
            match argsArray.size with
            | 2 => do
                let pyReduceNoInitIdent := mkIdent ``pyReduceNoInit
                let elemTy? ← inferIterableElemTypeSyntax? argsArray[1]!
                let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! elemTy?
                let adjustedCodes := #[funcCode, argsCodes[1]!]
                return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                  let f := resolvedArgs[0]!
                  let xs := resolvedArgs[1]!
                  `($pyReduceNoInitIdent $xs $f)
            | 3 => do
                let pyReduceIdent := mkIdent ``pyReduce
                let initTy? ← inferSimpleValueTypeSyntax? argsArray[2]!
                let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! initTy?
                let adjustedCodes := #[funcCode, argsCodes[1]!, argsCodes[2]!]
                return ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                  let f := resolvedArgs[0]!
                  let xs := resolvedArgs[1]!
                  let init := resolvedArgs[2]!
                  `($pyReduceIdent $xs $f $init)
            | _ =>
                throwError "reduce() expects two or three positional arguments."
        | .ok "Name", .ok funcName =>
            let mappedName ← leanName funcName.toName
            funcIdent := (mkIdent mappedName : TSyntax `term)
        | _, _ =>
            funcIdent ← getCode funcJson `term

    for argCode in argsCodes do
      allArgs := allArgs.push argCode
    for argJson in argsArray do
      allArgJsons := allArgJsons.push argJson

    let buildApplied : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolvedArgs => do
      let mut t ← `($funcIdent $resolvedArgs*)
      for (kwName, kwValueJson) in keyWordsMap.toList do
        let kwValueCode ← getCode kwValueJson `term
        let kwId := mkIdent kwName.toName
        t ← `($t ($kwId:ident := $kwValueCode))
      return t

    if allArgJsons.toList.any basicJsonUsesIOEffect then
      return ← buildIOPureApplicationFromArgs allArgJsons allArgs buildApplied
    else
      return ← buildApplied allArgs
  | `doElem, json => do
    let .ok funcJson := json.getObjValAs? Json "func" | throwError
      s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
    let .ok argsJson := json.getObjValAs? Json "args" | throwError
      s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
    let argsArray ← match argsJson with
      | .arr arr => pure arr
      | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
    let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
      s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
    let .ok keyWordsMap := keyWordsJson.getObj? | throwError
      s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"

    let argsCodes ← argsArray.mapM (fun argJson => getCode argJson `term)

    let mut allArgs : Array (TSyntax `term) := #[]
    let mut allArgJsons : Array Json := #[]
    let mut funcIdent : TSyntax `term ← `("")

    match ← jsonLibraryMappedName? funcJson with
    | some leanName =>
        funcIdent := (mkIdent leanName : TSyntax `term)
    | none =>
      if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
        let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
          s!"Attribute node missing 'value' field: {funcJson}"
        let .ok attr := funcJson.getObjValAs? String "attr" | throwError
          s!"Attribute node missing 'attr' field: {funcJson}"

        if attr == "reduce" && valueJson.getObjValAs? String "node_type" == .ok "Name" &&
            valueJson.getObjValAs? String "id" == .ok "functools" then
          unless keyWordsMap.isEmpty do
            throwError "functools.reduce() keyword arguments are not supported yet."
          let t ← match argsArray.size with
            | 2 => do
                let pyReduceNoInitIdent := mkIdent ``pyReduceNoInit
                let elemTy? ← inferIterableElemTypeSyntax? argsArray[1]!
                let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! elemTy?
                let adjustedCodes := #[funcCode, argsCodes[1]!]
                buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                  let f := resolvedArgs[0]!
                  let xs := resolvedArgs[1]!
                  `($pyReduceNoInitIdent $xs $f)
            | 3 => do
                let pyReduceIdent := mkIdent ``pyReduce
                let initTy? ← inferSimpleValueTypeSyntax? argsArray[2]!
                let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! initTy?
                let adjustedCodes := #[funcCode, argsCodes[1]!, argsCodes[2]!]
                buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                  let f := resolvedArgs[0]!
                  let xs := resolvedArgs[1]!
                  let init := resolvedArgs[2]!
                  `($pyReduceIdent $xs $f $init)
            | _ =>
                throwError "functools.reduce() expects two or three positional arguments."
          if argsArray.toList.any basicJsonUsesMonadicEffect then
            return ← `(doElem| let _ ← $t:term)
          else
            return ← `(doElem| let _ := $t)

        if attr == "append" then
          unless keyWordsMap.isEmpty do
            throwError "append() calls do not support keyword arguments."
          let some argJson := argsArray[0]? | throwError "append() expects exactly one positional argument."
          unless argsArray.size == 1 do
            throwError "append() expects exactly one positional argument."
          let targetIdent ← getCode valueJson `ident
          let argCode ← getCode argJson `term
          let pyAppendIdent := mkIdent ``pyAppend
          return ← `(doElem| $targetIdent:ident := $pyAppendIdent $targetIdent $argCode)

        if attr == "get" then
          unless keyWordsMap.isEmpty do
            throwError "get() calls with keyword arguments are not supported yet."
          let valCode ← getCode valueJson `term
          let t ← match argsArray.size with
            | 1 =>
                let keyCode ← getCode argsArray[0]! `term
                let pyGetOptIdent := mkIdent ``pyGetOpt
                `($pyGetOptIdent $valCode $keyCode)
            | 2 =>
                let keyCode ← getCode argsArray[0]! `term
                let defaultCode ← getCode argsArray[1]! `term
                let pyGetDIdent := mkIdent ``pyGetD
                `($pyGetDIdent $valCode $keyCode $defaultCode)
            | _ =>
                throwError "get() expects one or two positional arguments."
          return ← `(doElem| let _ := $t)

        if attr == "sort" then
          unless keyWordsMap.isEmpty do
            throwError "sort() calls do not support keyword arguments yet."
          unless argsArray.isEmpty do
            throwError "sort() expects no positional arguments."
          let targetIdent ← getCode valueJson `ident
          let pySortIdent := mkIdent ``pySort
          return ← `(doElem| $targetIdent:ident := $pySortIdent $targetIdent)

        let valCode ← getCode valueJson `term
        allArgs := allArgs.push valCode
        allArgJsons := allArgJsons.push valueJson

        match pythonMethodMap attr with
        | some funcName =>
            funcIdent := mkIdent funcName
        | none =>
            throwError s!"Unsupported Python method '{attr}' encountered in Call node."
      else
        match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
        | .ok "Name", .ok "print" => do
            let supportedKeywords := ["sep", "end"]
            for (kwName, _) in keyWordsMap.toList do
              unless supportedKeywords.contains kwName do
                throwError s!"print() keyword argument '{kwName}' is not supported yet."
            let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let pyPrintIOIdent := mkIdent ``pyPrintIO
              match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
              | none, none =>
                  `($pyPrintIOIdent [$resolvedArgs,*])
              | _, _ =>
                  let sepCode ← match keyWordsMap.get? "sep" with
                    | some sepJson => getCode sepJson `term
                    | none => `(" ")
                  let endCode ← match keyWordsMap.get? "end" with
                    | some endJson => getCode endJson `term
                    | none => `("\n")
                  `($pyPrintIOIdent [$resolvedArgs,*] $sepCode $endCode)
            return ← `(doElem| let _ ← $t:term)
        | .ok "Name", .ok "input" => do
            unless keyWordsMap.isEmpty do
              throwError "input() keyword arguments are not supported yet."
            unless argsArray.size ≤ 1 do
              throwError "input() expects zero or one positional argument."
            let pyInputIOIdent := mkIdent ``pyInputIO
            let t ← buildIOActionApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              match resolvedArgs.size with
              | 0 => `($pyInputIOIdent "")
              | 1 =>
                  let arg0 := resolvedArgs[0]!
                  `($pyInputIOIdent $arg0)
              | _ => throwError "input() expects zero or one positional argument."
            return ← `(doElem| let _ ← $t:term)
        | .ok "Name", .ok "int" => do
            unless keyWordsMap.isEmpty do
              throwError "int() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "int() expects exactly one positional argument."
            let pyIntIdent := mkIdent ``pyInt
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyIntIdent $arg0)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "str" => do
            unless keyWordsMap.isEmpty do
              throwError "str() keyword arguments are not supported yet."
            let t ← match argsArray.size with
              | 0 => `("")
              | 1 =>
                  let pyStrIdent := mkIdent ``pyStr
                  buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
                    let arg0 := resolvedArgs[0]!
                    `($pyStrIdent $arg0)
              | _ =>
                  throwError "str() expects zero or one positional argument."
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "list" => do
            unless keyWordsMap.isEmpty do
              throwError "list() keyword arguments are not supported yet."
            unless argsArray.size == 1 do
              throwError "list() currently expects exactly one positional argument."
            let pyListIdent := mkIdent ``pyList
            let t ← buildIOPureApplicationFromArgs argsArray argsCodes fun resolvedArgs => do
              let arg0 := resolvedArgs[0]!
              `($pyListIdent $arg0)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "map" => do
            unless keyWordsMap.isEmpty do
              throwError "map() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "map() currently expects exactly two positional arguments."
            let pyMapIdent := mkIdent ``pyMap
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            let t ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyMapIdent $f $xs)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "filter" => do
            unless keyWordsMap.isEmpty do
              throwError "filter() keyword arguments are not supported yet."
            unless argsArray.size == 2 do
              throwError "filter() currently expects exactly two positional arguments."
            let pyFilterIdent := mkIdent ``pyFilter
            let funcCode ← mappedCallableValueCode argsArray[0]!
            let adjustedCodes := #[funcCode, argsCodes[1]!]
            let t ← buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
              let f := resolvedArgs[0]!
              let xs := resolvedArgs[1]!
              `($pyFilterIdent $f $xs)
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok "reduce" => do
            unless keyWordsMap.isEmpty do
              throwError "reduce() keyword arguments are not supported yet."
            let t ← match argsArray.size with
              | 2 => do
                  let pyReduceNoInitIdent := mkIdent ``pyReduceNoInit
                  let elemTy? ← inferIterableElemTypeSyntax? argsArray[1]!
                  let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! elemTy?
                  let adjustedCodes := #[funcCode, argsCodes[1]!]
                  buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                    let f := resolvedArgs[0]!
                    let xs := resolvedArgs[1]!
                    `($pyReduceNoInitIdent $xs $f)
              | 3 => do
                  let pyReduceIdent := mkIdent ``pyReduce
                  let initTy? ← inferSimpleValueTypeSyntax? argsArray[2]!
                  let funcCode ← typedReduceLambdaCode argsArray[0]! argsCodes[0]! initTy?
                  let adjustedCodes := #[funcCode, argsCodes[1]!, argsCodes[2]!]
                  buildIOPureApplicationFromArgs argsArray adjustedCodes fun resolvedArgs => do
                    let f := resolvedArgs[0]!
                    let xs := resolvedArgs[1]!
                    let init := resolvedArgs[2]!
                    `($pyReduceIdent $xs $f $init)
              | _ =>
                  throwError "reduce() expects two or three positional arguments."
            if argsArray.toList.any basicJsonUsesMonadicEffect then
              return ← `(doElem| let _ ← $t:term)
            else
              return ← `(doElem| let _ := $t)
        | .ok "Name", .ok funcName =>
            let mappedName ← leanName funcName.toName
            funcIdent := (mkIdent mappedName : TSyntax `term)
        | _, _ =>
            funcIdent ← getCode funcJson `term

    for argCode in argsCodes do
      allArgs := allArgs.push argCode
    for argJson in argsArray do
      allArgJsons := allArgJsons.push argJson

    let buildApplied : Array (TSyntax `term) → PygenM (TSyntax `term) := fun resolvedArgs => do
      let mut t ← `($funcIdent $resolvedArgs*)
      for (kwName, kwValueJson) in keyWordsMap.toList do
        let kwValueCode ← getCode kwValueJson `term
        let kwId := mkIdent kwName.toName
        t ← `($t ($kwId:ident := $kwValueCode))
      return t

    if allArgJsons.toList.any basicJsonUsesIOEffect then
      let t ← buildIOPureApplicationFromArgs allArgJsons allArgs buildApplied
      `(doElem| let _ ← $t:term)
    else
      let t ← buildApplied allArgs
      `(doElem| let _ := $t)
  | _, _ => throwError s!"Unsupported syntax category for Call node"

@[pygen "Attribute"]
def attributeSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName =>
        pure (mkIdent leanName)
    | none =>
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok attr := json.getObjValAs? String "attr" | throwError
          s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
        let valueCode ← getCode valueJson `term
        let attrId := mkIdent attr.toName
        `($valueCode.$attrId)
  | `ident, json => do
    match ← jsonLibraryMappedName? json with
    | some leanName =>
        pure (mkIdent leanName)
    | none =>
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Attribute node does not have a 'value' field or it is not a JSON value: {json}"
        let .ok attr := json.getObjValAs? String "attr" | throwError
          s!"Attribute node does not have an 'attr' field or it is not a string: {json}"
        let id ← getCode valueJson `ident
        return mkIdent <| id.getId ++ attr.toName
  | _, _ => throwError s!"Unsupported syntax category for Attribute node"

end PyAstLean
