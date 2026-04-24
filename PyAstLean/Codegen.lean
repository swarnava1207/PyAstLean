import Lean
import Qq

open Lean Meta Elab Term Qq

namespace PyAstLean

/-!
## Code generation from JSON data

This module provides a way to generate Lean code from JSON data in an extensible way. The main function is `getCode`, which takes a `CodeGenerator` a Json object and a syntax category, and returns the corresponding syntax (in the monad `TermElabM`) or throws an error.
-/

initialize
  registerTraceClass `pyastlean.codegen.info
  registerTraceClass `pyastlean.codegen.debug


instance : Repr SyntaxNodeKinds where
  reprPrec kinds n :=
    let names : List Name := kinds
    Repr.reprPrec names n

instance : ToString SyntaxNodeKinds where
  toString kinds :=
    let names : List Name := kinds
    ToString.toString names

/-- Environment extension storing code generation lemmas -/
initialize codegenExt :
    SimpleScopedEnvExtension (Name × String) (Std.HashMap String (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key) =>
        m.insert key <| (m.getD key #[] ).push n
    initial := {}
  }

/--
Attribute for generating Lean code, more precisely Syntax of a given category, from JSON data. More precisely, we generate `TermElabM <| TSyntax kind` from a JSON object, with the matching key as part of the attribute.

As the same statement can generate different syntax categories (e.g. `def` and `let`) this is not specified in the attribute. Instead the target category is part of the signature of the function.
-/
syntax (name := codegen) "codegen" (str,*) : attr

/--
Extract the keys from the `codegen` attribute syntax. Returns an array of strings.
-/
def codegenKeyM (stx : Syntax) : CoreM <| Array String := do
  match stx with
  | `(attr|codegen $x) => do
    return #[x.getString]
  | `(attr|codegen $xs,*) => do
    let keys := xs.getElems
    return keys.map (·.getString)
  | _ => throwUnsupportedSyntax

/--
An environment extension for code generation functions. It stores the functions that can be used to generate code from JSON data. The key is a string that identifies the function, and the value is an array of names of the functions that can be used to generate code for that key.
-/
initialize registerBuiltinAttribute {
  name := `codegen
  descr := "Lean code generator"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    -- Obtained from Qq.
    let expectedType : Q(Type) := q(Syntax →  (kind : SyntaxNodeKinds) →  (json : Json) → TermElabM (TSyntax kind))
    unless ← isDefEq declTy expectedType do
      throwError -- replace with error
        s!"codegen: {decl} has type {declTy}, but expected {expectedType}"
    let keys ← codegenKeyM stx
    trace[pyastlean.codegen.debug] m!"codegen: {decl}; keys: {keys}"
    for key in keys do
      codegenExt.add (decl, key) kind
}


/--
Get the code generation functions for a given key. The key is a string that identifies the function. If no function is found for the key, an error is thrown.
-/
def codegenMatches (key: String) : CoreM <| Array Name := do
  let allKeys := (codegenExt.getState (← getEnv)).toArray.map (fun (k, _) => k)
  let some fs :=
    (codegenExt.getState (← getEnv)).get? key | throwError
      s!"codegen: no function found for key '{key}' available keys are {allKeys.toList}"
  trace[pyastlean.codegen.info] m!"found {fs.size} functions for key {key}"
  if fs.isEmpty then
    trace[pyastlean.codegen.debug] m!"no function found for key {key} in {allKeys.toList}"
  return fs
