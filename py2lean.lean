import Lean
import PyAstLean
open Lean Meta Elab Term Qq Std
open PyAstLean

unsafe def main(args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  match args[0]? with
  | some jsStr =>
    let env ←
    importModules (loadExts := true) #[
    {module := `PyAstLean},
    {module := `Mathlib}] {}
    let ctx: Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}}
    match Json.parse jsStr with
    | .ok jsonTask =>
      let .ok task := jsonTask.getObjValAs? String "task" | IO.println "Invalid JSON: missing 'task' field or it is not a string"
      match task with
      | "translate_expr" =>
        let .ok json := jsonTask.getObjValAs? Json "ast" | IO.println "Invalid JSON: missing 'ast' field or it is not a JSON value"
        let code? ← getCodeTermIO json ctx env
        match code? with
        | .ok code =>
          let jsCode := Json.mkObj [("result", Json.bool true), ("lean_expression", code.pretty)]
          IO.println jsCode
        | .error err =>
          let jsCode := Json.mkObj [("result", Json.bool false), ("error", Json.str err)]
          IO.println jsCode
      | _ => IO.println s!"Unknown task: {task}"
    | .error err => IO.println s!"Error parsing JSON: {err}"
  | none => IO.println "No JSON input provided"
