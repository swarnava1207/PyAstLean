import Mathlib
import PyAstLean.PyAPI.CommonProtocols.Iterable
import PyAstLean.PyAPI.PyPrint

namespace PyAstLean

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

/--
Python-style `str(...)` coercion.

This reuses the printing runtime so values render with the same Python-like surface as
they would inside `print(...)`.
-/
def pyStr {α : Type} [PyPrintable α] (x : α) : String :=
  pyStringify x

/--
Python-style eager `list(...)` coercion.

This currently follows the iterable protocol, so strings become character lists,
lists stay lists, and dictionaries become their key lists.
-/
def pyList {α β : Type} [PyIterable α β] (x : α) : List β :=
  pyIter x

end PyAstLean
