import Lean

/-!
A linter that flags every best-effort placeholder (`pyUnsupported` / `pyUnsupportedUnit` /
`pyUnsupportedVal`) emitted by `py2lean`'s best-effort fallback. Each use site gets a yellow
"not supported" warning in the editor, so degraded lines are impossible to miss — without the
"deprecated" framing (these are not deprecated; they're transpiler placeholders).
-/

open Lean Elab Command

namespace PyAstLean.Linter

register_option linter.unsupported : Bool := {
  defValue := true
  descr := "warn on best-effort `pyUnsupported(...)` placeholders for Python constructs the \
            transpiler does not support"
}

/-- True for an identifier whose final component is one of the placeholder names. -/
private def isUnsupportedName (nm : Name) : Bool :=
  match nm.eraseMacroScopes with
  | .str _ s => s == "pyUnsupported" || s == "pyUnsupportedUnit" || s == "pyUnsupportedVal"
  | _ => false

/-- Collect every identifier occurrence of a placeholder name in a syntax tree. -/
private partial def collect : Syntax → Array Syntax → Array Syntax
  | stx@(Syntax.ident ..), acc => if isUnsupportedName stx.getId then acc.push stx else acc
  | Syntax.node _ _ args, acc => args.foldl (fun a s => collect s a) acc
  | _, acc => acc

/-- The linter: warn at each placeholder use site. -/
def unsupportedLinter : Linter where
  run := fun stx => do
    unless Linter.getLinterValue linter.unsupported (← Linter.getLinterOptions) do
      return
    for occ in collect stx #[] do
      Linter.logLint linter.unsupported occ
        m!"Code is unsupported for transpilation to Lean. \
           (the original Python source is in the string argument)"

initialize addLinter unsupportedLinter

end PyAstLean.Linter
