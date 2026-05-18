import Mathlib

namespace PyAstLean

/-- Concrete list implementation for Python-style `append`. -/
def pyListAppend : List α → α → List α
  | lst, elem => lst ++ [elem]

/--
Public runtime surface for Python `append`.

Keep codegen targeting `pyAppend`; if another runtime type later needs append-like
behavior, this public name can be promoted to a protocol without changing the
generated Lean surface.
-/
def pyAppend : List α → α → List α :=
  pyListAppend

/--
Concrete list implementation for Python-style `pop(index)`.

If the index is out of bounds, return the provided default and leave the list unchanged.
-/
def pyListPop (xs : List α) (idx : Int) (default : Option α := none) : (Option α × List α) :=
  if 0 <= idx then
    let natIdx := idx.toNat
    if hUpper : natIdx < xs.length then
      let value := xs.get ⟨natIdx, hUpper⟩
      (some value, xs.eraseIdx natIdx)
    else
      (default, xs)
  else
    (default, xs)

/--
API for `list.extend()` which concatenates two lists.
-/
def pyListExtend (xs : List α) (ys : List α) : List α :=
  xs ++ ys

/-- Public runtime surface for Python `extend()`. -/
def pyExtend : List α → List α → List α :=
  pyListExtend

/--
API for `list.index()` which returns the index of the first occurrence of the given
element in the list, or raises at runtime when the element is missing.
-/
def pyListIndex [DecidableEq α] (xs : List α) (elem : α) : Int :=
  match xs.findIdx? (fun x => x = elem) with
  | some idx => idx
  | none => panic! s!"ValueError: Element is not in list"

/-- Public runtime surface for Python `index()`. -/
def pyIndex [DecidableEq α] : List α → α → Int :=
  pyListIndex

/--
API for `list.count(elem)` which returns the number of occurrences of the given element in the list.
-/
def PyListCount [DecidableEq α] (xs : List α) (elem : α) : Nat :=
  xs.count elem

/-- Public runtime surface for Python `count()`. -/
def pyCount [DecidableEq α] : List α → α → Nat :=
  PyListCount

def pyListReverse (xs : List α) : List α :=
  xs.reverse

/-- Public runtime surface for Python `reverse()`. -/
def pyReverse : List α → List α :=
  pyListReverse

/-- Public runtime surface for Python `clear()`. -/
def pyListClear (_ : List α) : List α :=
  []

def pyClear (xs : List α) : List α :=
  pyListClear xs

/-- API runtime surface for Python `insert()`. -/
def pyListInsert (xs : List α) (idx : Int) (elem : α) : List α :=
  if 0 <= idx then
    let natIdx := idx.toNat
    if natIdx <= xs.length then
      xs.take natIdx ++ [elem] ++ xs.drop natIdx
    else
      xs ++ [elem]
  else
    -- Python prepends when given a negative index
    [elem] ++ xs

/-- Public runtime surface for Python `insert()`. -/
def pyInsert : List α → Int → α → List α :=
  pyListInsert

end PyAstLean
