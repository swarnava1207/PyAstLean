import PyAstLean.PyGens.Utils

open Lean Meta Elab Term Qq Std

namespace PyAstLean

/-- Lower `String.startsWith` as syntax so exception handlers can inspect thrown strings. -/
def stringStartsWithTerm (s prefixTerm : TSyntax `term) : PygenM (TSyntax `term) := do
  let startsWithIdent := mkIdent ``String.startsWith
  `($startsWithIdent $s $prefixTerm)

/-- Raise a string-valued exception using a parseable term form rather than pretty-printer sugar. -/
def throwStringDoElemSyntax (value : TSyntax `term) : PygenM (TSyntax `doElem) := do
  `(doElem| throwThe String $value)

/-- Recover the exception constructor name from the JSON term used in `raise` / `except`. -/
def exceptionNameFromTermJson (json : Json) : PygenM String := do
  let .ok nodeType := json.getObjValAs? String "node_type" | throwError
    s!"Exception term is missing a 'node_type' field: {json}"
  match nodeType with
  | "Name" =>
      let .ok id := json.getObjValAs? String "id" | throwError
        s!"Exception name node is missing an 'id': {json}"
      return id
  | "Attribute" =>
      let .ok attr := json.getObjValAs? String "attr" | throwError
        s!"Exception attribute node is missing an 'attr': {json}"
      return attr
  | _ =>
      throwError s!"Unsupported exception type node: {nodeType}"

/-- Lower a Python `raise` payload into the string currently used by the exception model. -/
def exceptionValueTerm (excJson? : Option Json) : PygenM (TSyntax `term) := do
  match excJson? with
  | none => `( "Python raise" )
  | some excJson =>
      let .ok nodeType := excJson.getObjValAs? String "node_type" | throwError
        s!"Raise node exception term is missing a 'node_type' field: {excJson}"
      match nodeType with
      | "Call" =>
          let .ok funcJson := excJson.getObjValAs? Json "func" | throwError
            s!"Raise call is missing a 'func' field: {excJson}"
          let excName ← exceptionNameFromTermJson funcJson
          let .ok argsJson := excJson.getObjValAs? (Array Json) "args" | throwError
            s!"Raise call is missing an 'args' field: {excJson}"
          match argsJson[0]? with
          | some firstArg =>
              let argTerm ← getCode firstArg `term
              let prefixStx := Syntax.mkStrLit s!"{excName}: "
              let appendIdent := mkIdent ``String.append
              let toStringIdent := mkIdent ``toString
              `($appendIdent $prefixStx ($toStringIdent $argTerm))
          | none =>
              return Syntax.mkStrLit excName
      | _ =>
          getCode excJson `term

/-- Build the guard deciding whether a caught exception should enter a given handler. -/
def handlerConditionTerm (caughtIdent : TSyntax `ident) (handlerType? : Option Json) : PygenM (TSyntax `term) := do
  match handlerType? with
  | none => pure trueTerm
  | some handlerTypeJson =>
      let .ok nodeType := handlerTypeJson.getObjValAs? String "node_type" | throwError
        s!"ExceptHandler type is missing a 'node_type' field: {handlerTypeJson}"
      match nodeType with
      | "Tuple" =>
          let .ok eltsJson := handlerTypeJson.getObjValAs? (Array Json) "elts" | throwError
            s!"Tuple handler type is missing an 'elts' field: {handlerTypeJson}"
          let mut cond? : Option (TSyntax `term) := none
          for elt in eltsJson do
            let excName := (← exceptionNameFromTermJson elt)
            let prefixStx := Syntax.mkStrLit s!"{excName}:"
            let altCond ← stringStartsWithTerm caughtIdent prefixStx
            cond? ← match cond? with
              | none => pure (some altCond)
              | some prev => pure (some (← orTerm prev altCond))
          pure <| cond?.getD falseTerm
      | _ =>
          let excName ← exceptionNameFromTermJson handlerTypeJson
          let prefixStx := Syntax.mkStrLit s!"{excName}:"
          stringStartsWithTerm caughtIdent prefixStx

/-- Compile the `except` chain into nested handler tests over the caught exception value. -/
partial def exceptHandlersDoElemSyntax (caughtIdent : TSyntax `ident) (handlers : List Json) :
    PygenM (TSyntax `doElem) := do
  match handlers with
  | [] => throwStringDoElemSyntax caughtIdent
  | handlerJson :: restHandlers => do
      let handlerType? := jsonFieldOption handlerJson "type"
      let handlerName? := handlerJson.getObjValAs? String "name" |>.toOption
      let .ok bodyElemsJson := handlerJson.getObjValAs? (Array Json) "body" | throwError
        s!"ExceptHandler node is missing a 'body' field: {handlerJson}"
      let cond ← handlerConditionTerm caughtIdent handlerType?
      let mut bodyElems := #[]
      if let some handlerName := handlerName? then
        bodyElems := bodyElems.push (← `(doElem| let $(mkIdent handlerName.toName) := $caughtIdent))
      bodyElems := bodyElems ++ (← monadicFunctionBodySyntax bodyElemsJson)
      let noop ← noopDoElemSyntax
      let bodyStx ← sequenceDoElems bodyElems noop
      let nextHandler ← exceptHandlersDoElemSyntax caughtIdent restHandlers
      `(doElem| if $cond then
          $bodyStx:doElem
        else
          $nextHandler:doElem)

@[pygen "Raise"]
def raiseSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let excJson? := jsonFieldOption json "exc"
        let excTerm ← exceptionValueTerm excJson?
        throwStringDoElemSyntax excTerm
    | _, _ => throwError s!"Unsupported syntax category for Raise node"

@[pygen "Try"]
def trySyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Try node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok handlersElems := json.getObjValAs? (Array Json) "handlers" | throwError
          s!"Try node does not have a 'handlers' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"Try node does not have an 'orelse' field or it is not a JSON array: {json}"
        let .ok finalbodyElems := json.getObjValAs? (Array Json) "finalbody" | throwError
          s!"Try node does not have a 'finalbody' field or it is not a JSON array: {json}"
        let bodyAndElse ← monadicFunctionBodySyntax (bodyElems ++ orelseElems)
        let catchIdent := mkIdent `caught
        let catchBody ← exceptHandlersDoElemSyntax catchIdent handlersElems.toList
        let noop ← noopDoElemSyntax
        let bodyStx ← sequenceDoElems bodyAndElse noop
        if finalbodyElems.isEmpty then
          `(doElem| try
              $bodyStx:doElem
            catch $catchIdent =>
              $catchBody:doElem)
        else
          let finalElems ← monadicFunctionBodySyntax finalbodyElems
          `(doElem| try
              $bodyStx:doElem
            catch $catchIdent =>
              $catchBody:doElem
            finally
              $[$finalElems:doElem]*)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | _, _ => throwError s!"Unsupported syntax category for Try node"

end PyAstLean
