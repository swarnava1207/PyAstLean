import Mathlib
import PyAstLean.PyAPI.CommonProtocols.Iterable
import PyAstLean.PyAPI.Operators

namespace PyAstLean

/--
Python-style eager `map`.

Unlike Python's lazy iterator result, the current runtime surface returns a `List`, which
fits the rest of the Lean-facing runtime well and keeps later consumers straightforward.
-/
def pyMap {α β γ : Type} [inst : PyIterable α β] (f : β → γ) (xs : α) : List γ :=
  (pyIter xs).map f

/-- Python-style eager `filter`, returning the kept elements as a `List`. -/
def pyFilter {α β : Type} [inst : PyIterable α β] (p : β → Bool) (xs : α) : List β :=
  (pyIter xs).filter p

/-- Python-style `zip`, truncating to the shorter iterable. -/
def pyZip {α β γ δ : Type} [instA : PyIterable α β] [instB : PyIterable γ δ]
    (xs : α) (ys : γ) : List (β × δ) :=
  (pyIter xs).zip (pyIter ys)

/-- Helper for Python-style `enumerate`, using `Int` indices to match the runtime's numeric story. -/
private def pyEnumerateFrom (start : Int) : List α → List (Int × α)
  | [] => []
  | x :: xs => (start, x) :: pyEnumerateFrom (start + 1) xs

/-- Python-style eager `enumerate`, defaulting to a `0` start index. -/
def pyEnumerate {α β : Type} [inst : PyIterable α β] (xs : α) (start : Int := 0) : List (Int × β) :=
  pyEnumerateFrom start (pyIter xs)

/-- Python-style `sum`, folding with the runtime addition operator and optional start value. -/
def pySum {α β : Type} [inst : PyIterable α β] [OfNat β 0]
    [PyHAdd β β β] (xs : α) (start : β := 0) : β :=
  (pyIter xs).foldl (fun acc x => acc +ₚ x) start

/-- Pick the minimum element of a non-empty list using `Ord`. -/
private def pyMinList [Ord α] [Inhabited α] : List α → α
  | [] => panic! "ValueError: min() arg is an empty sequence"
  | x :: xs =>
      xs.foldl
        (fun best y => if compare y best == Ordering.lt then y else best)
        x

/-- Python-style `min` over one iterable argument. -/
def pyMin {α β : Type} [inst : PyIterable α β] [Ord β] [Inhabited β] (xs : α) : β :=
  pyMinList (pyIter xs)

/-- Pick the maximum element of a non-empty list using `Ord`. -/
private def pyMaxList [Ord α] [Inhabited α] : List α → α
  | [] => panic! "ValueError: max() arg is an empty sequence"
  | x :: xs =>
      xs.foldl
        (fun best y => if compare y best == Ordering.gt then y else best)
        x

/-- Python-style `max` over one iterable argument. -/
def pyMax {α β : Type} [inst : PyIterable α β] [Ord β] [Inhabited β] (xs : α) : β :=
  pyMaxList (pyIter xs)

/--
Python-style `reduce(function, iterable, initializer)`.

The iterable comes first in the Lean helper so instance resolution can learn the
element type before elaborating the reducer lambda. That keeps overloaded arithmetic
inside generated lambdas much more predictable.
-/
def pyReduce {α β : Type} [inst : PyIterable α β] (xs : α)
    (f : β → β → β) (init : β) : β :=
  (pyIter xs).foldl f init

/--
Python-style `reduce(function, iterable)` without an initializer.

This follows Python's runtime behavior and errors on an empty sequence.
-/
def pyReduceNoInit {α β : Type} [inst : PyIterable α β] [Inhabited β] (xs : α)
    (f : β → β → β) : β :=
  match pyIter xs with
  | [] => panic! "TypeError: reduce() of empty iterable with no initial value"
  | x :: rest => rest.foldl f x

end PyAstLean
