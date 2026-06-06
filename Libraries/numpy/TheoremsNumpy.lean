import Mathlib
import Libraries.numpy.NumpyDef
import Libraries.numpy.Creation
import Libraries.numpy.Statistics

/-!
# Correctness theorems for the `numpy` runtime surface

Structural guarantees about the NumPy-style helpers: the *shapes* the constructors produce, and
the *lengths* the elementwise/reduction helpers preserve. These are the properties downstream
code silently relies on (a `zeros((r, c))` really has `r` rows of `c` columns; `cumsum` keeps the
vector length; `diff` drops exactly one element). Numeric-value identities over `Float` are
omitted because IEEE-754 `Float` admits no useful algebraic rewriting in Lean.
-/

namespace Libraries.numpy

/-! ### Constructor shapes -/

/-- `zeros((r, c))` has exactly `r` rows. -/
@[simp] theorem pyNumpyRows_zeros (r c : Nat) :
    pyNumpyRows (pyNumpyZeros (Int.ofNat r, Int.ofNat c)) = r := by
  simp [pyNumpyRows, pyNumpyZeros, pyNumpyNatFromInt]

/-- `ones((r, c))` has exactly `r` rows. -/
@[simp] theorem pyNumpyRows_ones (r c : Nat) :
    pyNumpyRows (pyNumpyOnes (Int.ofNat r, Int.ofNat c)) = r := by
  simp [pyNumpyRows, pyNumpyOnes, pyNumpyNatFromInt]

/-- Every row of `zeros((r, c))` has exactly `c` columns, so the matrix is rectangular. -/
theorem pyNumpyZeros_isRectangular (r c : Nat) :
    pyNumpyIsRectangular (pyNumpyZeros (Int.ofNat r, Int.ofNat c)) = true := by
  simp [pyNumpyIsRectangular, pyNumpyZeros, pyNumpyNatFromInt, List.all_eq_true]

/-- `eye(n)` is a square matrix. -/
theorem pyNumpyEye_isSquare (n : Nat) :
    pyNumpyIsSquare (pyNumpyEye (Int.ofNat n)) = true := by
  simp [pyNumpyIsSquare, pyNumpyIsRectangular, pyNumpyEye, pyNumpyNatFromInt, List.all_eq_true]

/-- `full(shape, v)` and `zeros(shape)` agree on shape: both replicate the same way. -/
@[simp] theorem pyNumpyRows_full {α} [PyNumpyScalar α] (r c : Nat) (v : α) :
    pyNumpyRows (pyNumpyFull (Int.ofNat r, Int.ofNat c) v) = r := by
  simp [pyNumpyRows, pyNumpyFull, pyNumpyNatFromInt]

/-! ### Length-preserving vector ops -/

/-- `cumsum` preserves the length of the input vector. -/
@[simp] theorem pyNumpyCumsum_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyCumsum xs).length = xs.length := by
  unfold pyNumpyCumsum
  rw [pyNumpyToFloats]
  rw [show xs.map toFloat = xs.map toFloat from rfl]
  generalize xs.map toFloat = ys
  rw [List.length_map] at *
  clear xs
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      simp only [pyNumpyCumsum.go, List.length_cons]
      -- the accumulator does not affect the produced length
      have : ∀ a, (pyNumpyCumsum.go a (y :: ys)).length = (y :: ys).length := by
        intro a
        induction ys generalizing a y with
        | nil => rfl
        | cons z zs ih2 =>
            simp only [pyNumpyCumsum.go, List.length_cons]
            rw [ih2]
      rw [this]

/-- `cumprod` preserves the length of the input vector. -/
@[simp] theorem pyNumpyCumprod_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyCumprod xs).length = xs.length := by
  unfold pyNumpyCumprod
  rw [pyNumpyToFloats, List.length_map]
  have : ∀ (a : Float) (ys : List Float),
      (pyNumpyCumprod.go a ys).length = ys.length := by
    intro a ys
    induction ys generalizing a with
    | nil => rfl
    | cons z zs ih => simp only [pyNumpyCumprod.go, List.length_cons]; rw [ih]
  rw [this]

/-- `sign` preserves the length of the input vector. -/
@[simp] theorem pyNumpySign_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpySign xs).length = xs.length := by
  simp [pyNumpySign, pyNumpyToFloats]

/-- `abs` preserves the length of the input vector. -/
@[simp] theorem pyNumpyAbs_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyAbs xs).length = xs.length := by
  simp [pyNumpyAbs, pyNumpyToFloats]

/-- `clip` preserves the length of the input vector. -/
@[simp] theorem pyNumpyClip_length {α} [PyNumpyScalar α] (xs : List α) (lo hi : Float) :
    (pyNumpyClip xs lo hi).length = xs.length := by
  simp [pyNumpyClip, pyNumpyToFloats]

/-- `diff` removes exactly one element from a nonempty vector. -/
@[simp] theorem pyNumpyDiff_length {α} [PyNumpyScalar α] (xs : List α) :
    (pyNumpyDiff xs).length = xs.length - 1 := by
  simp [pyNumpyDiff, pyNumpyToFloats, List.length_zipWith]
  omega

end Libraries.numpy
