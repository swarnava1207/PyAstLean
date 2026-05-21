import Mathlib
import PyAstLean.PyAPI.Builtins.Casting

namespace PyAstLean

/-- Read one Python-style input line, optionally printing a prompt first. -/
def pyInputIO (prompt : String := "") : IO String := do
  if !prompt.isEmpty then
    IO.print prompt
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  return line.trimAsciiEnd.toString

end PyAstLean
