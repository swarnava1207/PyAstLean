import Mathlib

namespace PyAstLean

/-- Read one Python-style input line, optionally printing a prompt first. -/
def pyInputIO (prompt : String := "") : IO String := do
  if !prompt.isEmpty then
    IO.print prompt
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  return line.trimAsciiEnd.toString

/--
Typeclass for Python-style `int(...)` coercions used by translated code.

This intentionally keeps the current CP-oriented behavior forgiving: invalid strings
become `0` instead of raising, so `int(input())` stays simple in the current subset.
-/
class PyIntCast (α : Type) where
  pyInt : α → Int

/-- Dispatch Python-style integer coercions. -/
def pyInt {α : Type} [PyIntCast α] (x : α) : Int :=
  PyIntCast.pyInt x

instance : PyIntCast Int where
  pyInt x := x

instance : PyIntCast Nat where
  pyInt x := x

instance : PyIntCast Bool where
  pyInt
    | true => 1
    | false => 0

instance : PyIntCast String where
  pyInt s := s.trimAscii.toString.toInt? |>.getD 0

end PyAstLean
