import Libraries.math.MathDef
import Libraries.numpy.NumpyDef

namespace Libraries.numpy

/-- Convert NumPy scalars to floats. -/
def pyNumpyToFloats {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  xs.map toFloat

/-- Insert a float into a sorted list. -/
def pyNumpyInsertSorted (x : Float) : List Float -> List Float
  | [] => [x]
  | y :: ys => if x <= y then x :: y :: ys else y :: pyNumpyInsertSorted x ys

/-- Sort floats using insertion sort. -/
def pyNumpySortFloats : List Float -> List Float
  | [] => []
  | x :: xs => pyNumpyInsertSorted x (pyNumpySortFloats xs)

/-- Index pairs for `argsort`. -/
def pyNumpyInsertIndexed (x : Float × Nat) : List (Float × Nat) -> List (Float × Nat)
  | [] => [x]
  | y :: ys => if x.1 <= y.1 then x :: y :: ys else y :: pyNumpyInsertIndexed x ys

/-- Sort indexed values by the numeric component. -/
def pyNumpyArgsortFloats : List Float -> List Nat :=
  fun xs =>
    let indexed := (List.range xs.length).zip xs
    let sorted :=
      indexed.foldl
        (fun acc p => pyNumpyInsertIndexed (p.2, p.1) acc)
        []
    sorted.map (fun p => p.2)

/-- Helper for reductions on nonempty float lists. -/
def pyNumpyReduceFloats (f : Float -> Float -> Float) : List Float -> Float
  | [] => panic! "ValueError: reduction on an empty list"
  | x :: xs => xs.foldl f x

/-- Helper for indexed argmin/argmax. -/
def pyNumpyArgReduceFloats (better : Float -> Float -> Bool) : List Float -> Nat
  | [] => panic! "ValueError: reduction on an empty list"
  | x :: xs =>
      let rec go (best : Float) (bestIdx curIdx : Nat) : List Float -> Nat
        | [] => bestIdx
        | y :: ys =>
            if better y best then
              go y curIdx (curIdx + 1) ys
            else
              go best bestIdx (curIdx + 1) ys
      go x 0 1 xs

/-- Helper to access the `n`th element safely. -/
def pyNumpyGetD (xs : List Float) (n : Nat) (default : Float := 0.0) : Float :=
  xs.getD n default

/-- Sum a list of NumPy scalars. -/
def pyNumpySumVec {α} [PyNumpyScalar α] (xs : List α) : Float :=
  (pyNumpyToFloats xs).foldl (· + ·) 0.0

/-- Mean of a list of NumPy scalars. -/
def pyNumpyMeanVec {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := pyNumpyToFloats xs
  if ys.isEmpty then
    panic! "ValueError: mean() of an empty list is undefined"
  else
    ys.foldl (· + ·) 0.0 / Rat.toFloat (ys.length : Rat)

/-- Minimum of a nonempty list. -/
def pyNumpyMin {α} [PyNumpyScalar α] (xs : List α) : Float :=
  pyNumpyReduceFloats (fun a b => if b < a then b else a) (pyNumpyToFloats xs)

/-- Maximum of a nonempty list. -/
def pyNumpyMax {α} [PyNumpyScalar α] (xs : List α) : Float :=
  pyNumpyReduceFloats (fun a b => if b > a then b else a) (pyNumpyToFloats xs)

/-- Index of the minimum element. -/
def pyNumpyArgmin {α} [PyNumpyScalar α] (xs : List α) : Nat :=
  pyNumpyArgReduceFloats (fun a b => a < b) (pyNumpyToFloats xs)

/-- Index of the maximum element. -/
def pyNumpyArgmax {α} [PyNumpyScalar α] (xs : List α) : Nat :=
  pyNumpyArgReduceFloats (fun a b => a > b) (pyNumpyToFloats xs)

/-- Median of a list. -/
def pyNumpyMedian {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := pyNumpySortFloats (pyNumpyToFloats xs)
  match ys.length with
  | 0 => panic! "ValueError: median() of an empty list is undefined"
  | n + 1 =>
      if (n + 1) % 2 = 1 then
        ys.getD ((n + 1) / 2) 0.0
      else
        let hi := ys.getD ((n + 1) / 2) 0.0
        let lo := ys.getD (((n + 1) / 2) - 1) 0.0
        (lo + hi) / 2.0

/-- Population variance of a list. -/
def pyNumpyVar {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := pyNumpyToFloats xs
  if ys.isEmpty then
    panic! "ValueError: var() of an empty list is undefined"
  else
    let μ := ys.foldl (· + ·) 0.0 / Rat.toFloat (ys.length : Rat)
    ys.foldl (fun acc x => acc + (x - μ) * (x - μ)) 0.0 / Rat.toFloat (ys.length : Rat)

/-- Population standard deviation of a list. -/
def pyNumpyStd {α} [PyNumpyScalar α] (xs : List α) : Float :=
  Float.sqrt (pyNumpyVar xs)

/-- Convert a float percentile to a list index. -/
def pyNumpyPercentileIndex (n : Nat) (p : Float) : Nat :=
  let p' := if p < 0.0 then 0.0 else if p > 100.0 then 100.0 else p
  let idx := ((p' / 100.0) * Rat.toFloat ((n - 1) : Rat))
  Int.toNat (Libraries.math.floatToInt (Float.floor idx))

/-- Percentile using a nearest-rank style lookup. -/
def pyNumpyPercentile {α} [PyNumpyScalar α] (xs : List α) (p : Float) : Float :=
  let ys := pyNumpySortFloats (pyNumpyToFloats xs)
  match ys.length with
  | 0 => panic! "ValueError: percentile() of an empty list is undefined"
  | n + 1 => ys.getD (pyNumpyPercentileIndex (n + 1) p) 0.0

/-- Clip values to a closed interval. -/
def pyNumpyClip {α} [PyNumpyScalar α] (xs : List α) (lo hi : Float) : List Float :=
  (pyNumpyToFloats xs).map (fun x => if x < lo then lo else if x > hi then hi else x)

/-- Round values to the nearest integer-valued float. -/
def pyNumpyRound {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map (fun x =>
    if x < 0.0 then
      Float.ceil (x - 0.5)
    else
      Float.floor (x + 0.5))

/-- Exponential elementwise map. -/
def pyNumpyExp {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map Float.exp

/-- Natural log elementwise map. -/
def pyNumpyLog {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map Float.log

/-- Base-10 log elementwise map. -/
def pyNumpyLog10 {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map (fun x => Float.log x / Float.log 10.0)

/-- Base-2 log elementwise map. -/
def pyNumpyLog2 {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map (fun x => Float.log x / Float.log 2.0)

/-- Square root elementwise map. -/
def pyNumpySqrt {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  (pyNumpyToFloats xs).map Float.sqrt

/-- Euclidean norm of a vector. -/
def pyNumpyNorm {α} [PyNumpyScalar α] (xs : List α) : Float :=
  let ys := pyNumpyToFloats xs
  Float.sqrt (ys.foldl (fun acc x => acc + x * x) 0.0)

/-- Logical `any` over a list. -/
def pyNumpyAny {α} [PyNumpyScalar α] (xs : List α) : Bool :=
  xs.any (fun x => toFloat x != 0.0)

/-- Logical `all` over a list. -/
def pyNumpyAll {α} [PyNumpyScalar α] (xs : List α) : Bool :=
  xs.all (fun x => toFloat x != 0.0)

/-- Elementwise membership test. -/
def pyNumpyIsin {α β} [PyNumpyScalar α] [PyNumpyScalar β] (xs : List α) (ys : List β) : List Bool :=
  let choices := pyNumpyToFloats ys
  (pyNumpyToFloats xs).map (fun x => choices.any (fun y => (x == y)))

/-- Elementwise boolean and. -/
def pyNumpyLogicalAnd (xs ys : List Bool) : List Bool :=
  List.zipWith (· && ·) xs ys

/-- Elementwise boolean or. -/
def pyNumpyLogicalOr (xs ys : List Bool) : List Bool :=
  List.zipWith (· || ·) xs ys

/-- Elementwise boolean not. -/
def pyNumpyLogicalNot (xs : List Bool) : List Bool :=
  xs.map not

/-- Elementwise closeness check. -/
def pyNumpyIsclose {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (xs : List α) (ys : List β) (tol : Float := 1e-8) : List Bool :=
  let lhs := pyNumpyToFloats xs
  let rhs := pyNumpyToFloats ys
  if lhs.length = rhs.length then
    List.zipWith (fun x y => Float.abs (x - y) ≤ tol) lhs rhs
  else
    panic! "ValueError: isclose() expects equal-length lists"

/-- Sort a list of scalars. -/
def pyNumpySort {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  pyNumpySortFloats (pyNumpyToFloats xs)

/-- Indices that would sort a list. -/
def pyNumpyArgsort {α} [PyNumpyScalar α] (xs : List α) : List Nat :=
  pyNumpyArgsortFloats (pyNumpyToFloats xs)

/-- First insertion point into a sorted list. -/
def pyNumpySearchsorted (sorted : List Float) (x : Float) : Nat :=
  let rec go : List Float -> Nat -> Nat
    | [] , idx => idx
    | y :: ys, idx => if x ≤ y then idx else go ys (idx + 1)
  go sorted 0

/-- Deduplicate a sorted list. -/
def pyNumpyUniqueFloats (xs : List Float) : List Float :=
  let rec go : Option Float → List Float → List Float
    | _, [] => []
    | none, y :: ys => y :: go (some y) ys
    | some prev, y :: ys =>
        if y == prev then
          go (some prev) ys
        else
          y :: go (some y) ys
  go none xs

/-- Unique values of a list. -/
def pyNumpyUnique {α} [PyNumpyScalar α] (xs : List α) : List Float :=
  pyNumpyUniqueFloats (pyNumpySort xs)

/-- Return values satisfying a boolean mask. -/
def pyNumpyWhere {α} [PyNumpyScalar α] (cond : List Bool) (x y : List α) : List Float :=
  let lhs := pyNumpyToFloats x
  let rhs := pyNumpyToFloats y
  if cond.length = lhs.length && lhs.length = rhs.length then
    let rec go : List Bool -> List Float -> List Float -> List Float
      | [], [], [] => []
      | c :: cs, tx :: xs, fx :: ys => (if c then tx else fx) :: go cs xs ys
      | _, _, _ => panic! "ValueError: where() expects equal-length lists"
    go cond lhs rhs
  else
    panic! "ValueError: where() expects equal-length lists"

/-- Indices of nonzero values. -/
def pyNumpyNonzero {α} [PyNumpyScalar α] (xs : List α) : List Nat :=
  let ys := pyNumpyToFloats xs
  let rec go : List Float -> Nat -> List Nat
    | [], _ => []
    | x :: rest, i => if x != 0.0 then i :: go rest (i + 1) else go rest (i + 1)
  go ys 0

/-- Coordinates of truthy values in a matrix-like boolean array. -/
def pyNumpyArgwhere (matrix : List (List Bool)) : List (Nat × Nat) :=
  let rec rowsGo : List (List Bool) -> Nat -> List (Nat × Nat)
    | [], _ => []
    | row :: rows, i =>
        let rec colsGo : List Bool -> Nat -> List (Nat × Nat)
          | [], _ => []
          | c :: cs, j => if c then (i, j) :: colsGo cs (j + 1) else colsGo cs (j + 1)
        colsGo row 0 ++ rowsGo rows (i + 1)
  rowsGo matrix 0

/-- Extract values satisfying a mask. -/
def pyNumpyExtract {α} [PyNumpyScalar α] (cond : List Bool) (xs : List α) : List Float :=
  let vals := pyNumpyToFloats xs
  if cond.length = vals.length then
    (List.zipWith (fun c x => if c then some x else none) cond vals).filterMap id
  else
    panic! "ValueError: extract() expects equal-length lists"

/-- Take elements at a list of indices. -/
def pyNumpyTake {α} [PyNumpyScalar α] (xs : List α) (indices : List Nat) : List Float :=
  let vals := pyNumpyToFloats xs
  indices.map (fun i => vals.getD i 0.0)

/-- Put values at a list of indices. -/
def pyNumpyPut {α} [PyNumpyScalar α] (xs : List α) (indices : List Nat) (values : List α) : List Float :=
  let vals := pyNumpyToFloats xs
  let reps := pyNumpyToFloats values
  if indices.length = reps.length then
    let rec go : List Float -> List Nat -> List Float -> List Float
      | [], [], _ => []
      | [], _ :: _, _ => []
      | x :: rest, idxs, repls =>
          match idxs, repls with
          | [], [] => x :: go rest [] []
          | i :: is, v :: vs =>
              if i = 0 then
                v :: go rest is vs
              else
                x :: go rest ((i - 1) :: is) (v :: vs)
          | _, _ => x :: go rest idxs repls
      go vals indices reps
  else
    panic! "ValueError: put() expects equal numbers of indices and values"

/-- Alias for Euclidean norm. -/
def pyNumpyLinalgNorm {α} [PyNumpyScalar α] (xs : List α) : Float :=
  pyNumpyNorm xs

/-- Remove a column from a row. -/
def pyNumpyRemoveIndex (xs : List Float) (idx : Nat) : List Float :=
  match xs, idx with
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, n + 1 => x :: pyNumpyRemoveIndex xs n

/-- Remove a row and column from a matrix. -/
def pyNumpyMinor (matrix : List (List Float)) (row col : Nat) : List (List Float) :=
  let rec goRows : List (List Float) -> Nat -> List (List Float)
    | [], _ => []
    | x :: xs, i =>
        if i = row then
          goRows xs (i + 1)
        else
          pyNumpyRemoveIndex x col :: goRows xs (i + 1)
  goRows matrix 0

/-- Determinant for square matrices, computed recursively. -/
partial def pyNumpyDet (matrix : List (List Float)) : Float :=
  if pyNumpyIsSquare matrix then
    match matrix with
    | [] => 1.0
    | [ [a] ] => a
    | [ [a, b], [c, d] ] => a * d - b * c
    | row :: _ =>
        let rec expand (cols : List Float) (j : Nat) : Float :=
          match cols with
          | [] => 0.0
          | a :: as =>
              let sign := if j % 2 = 0 then 1.0 else -1.0
              sign * a * pyNumpyDet (pyNumpyMinor matrix 0 j) + expand as (j + 1)
        expand row 0
  else
    panic! "ValueError: det() expects a square matrix"

/-- Inverse for 1x1 and 2x2 square matrices. -/
def pyNumpyInv (matrix : List (List Float)) : List (List Float) :=
  if pyNumpyIsSquare matrix then
    match matrix with
    | [ [a] ] =>
        if a == 0.0 then
          panic! "ValueError: singular matrix"
        else
          [[1.0 / a]]
    | [ [a, b], [c, d] ] =>
        let det := a * d - b * c
        if det == 0.0 then
          panic! "ValueError: singular matrix"
        else
          [[d / det, -b / det], [-c / det, a / det]]
    | _ => panic! "ValueError: inv() currently supports only 1x1 and 2x2 matrices"
  else
    panic! "ValueError: inv() expects a square matrix"

/-- Solve a linear system via a closed-form inverse. -/
def pyNumpySolve (matrix rhs : List (List Float)) : List (List Float) :=
  pyNumpyMatmul (pyNumpyInv matrix) rhs

end Libraries.numpy
