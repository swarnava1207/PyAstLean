import Mathlib

namespace PyAstLean

/--
Typeclass for Python-style iteration.

Use this when codegen should normalize different iterable runtime values into one
public Lean operation, `pyIter`, without caring which concrete type supplied the
elements.
-/
class PyIterable (α : Type) (β : outParam Type) where
  toPyList : α → List β

/-- Dispatch Python-style iteration through the `PyIterable` protocol. -/
def pyIter {α β : Type} [inst : PyIterable α β] (value : α) : List β :=
  inst.toPyList value

/-- Lists are already Python-style iterables. -/
instance : PyIterable (List α) α where
  toPyList := id

/-- Arrays iterate by converting to lists. -/
instance : PyIterable (Array α) α where
  toPyList := Array.toList

/-- Strings iterate over characters. -/
instance : PyIterable String Char where
  toPyList := String.toList

/-- Dictionaries iterate over keys, matching Python's default dictionary iteration. -/
instance [BEq α] [Hashable α] : PyIterable (Std.HashMap α β) α where
  toPyList m := m.toList.map Prod.fst

/--
Homogeneous 2-tuples can participate in Python-style iterable builtins by exposing
their elements as a two-element list.
-/
instance : PyIterable (α × α) α where
  toPyList p := [p.1, p.2]

end PyAstLean
