import Mathlib

namespace Libraries.numpy

/-- Types that can be treated as NumPy numeric entries by the runtime layer. -/
class PyNumpyScalar (α : Type) where
  toFloat : α → Float

export PyNumpyScalar (toFloat)

instance : PyNumpyScalar Float where
  toFloat := id

instance : PyNumpyScalar Rat where
  toFloat := Rat.toFloat

instance : PyNumpyScalar Int where
  toFloat x := Rat.toFloat (x : Rat)

instance : PyNumpyScalar Nat where
  toFloat x := Rat.toFloat (x : Rat)

instance : PyNumpyScalar Bool where
  toFloat b := if b then 1.0 else 0.0

/-- Convert a nonnegative `Int` dimension to `Nat`. -/
def pyNumpyNatFromInt (n : Int) : Nat :=
  if n < 0 then
    panic! "ValueError: numpy dimensions must be nonnegative"
  else
    n.toNat

/-- Number of rows in a matrix. -/
def pyNumpyRows {α} (matrix : List (List α)) : Nat :=
  matrix.length

/-- Number of columns in a matrix, taken from the first row. -/
def pyNumpyCols {α} (matrix : List (List α)) : Nat :=
  match matrix with
  | [] => 0
  | row :: _ => row.length

/-- Check that every row has the same length. -/
def pyNumpyIsRectangular {α} (matrix : List (List α)) : Bool :=
  match matrix with
  | [] => true
  | row :: rows => rows.all (fun r => r.length = row.length)

/-- Check that a matrix is square. -/
def pyNumpyIsSquare {α} (matrix : List (List α)) : Bool :=
  pyNumpyIsRectangular matrix &&
    match matrix with
    | [] => true
    | row :: _ => matrix.length = row.length

/-- Compare the shapes of two matrices. -/
def pyNumpySameShape? {α β} (lhs : List (List α)) (rhs : List (List β)) : Bool :=
  match lhs, rhs with
  | [], [] => true
  | l :: ls, r :: rs => l.length = r.length && pyNumpySameShape? ls rs
  | _, _ => false

/-- Normalize a matrix to `Float` entries. -/
def pyNumpyArray {α} [PyNumpyScalar α] (matrix : List (List α)) : List (List Float) :=
  matrix.map (List.map toFloat)

/-- Return the matrix shape as `(rows, cols)`. -/
def pyNumpyShape {α} (matrix : List (List α)) : Int × Int :=
  if pyNumpyIsRectangular matrix then
    (Int.ofNat matrix.length, Int.ofNat (pyNumpyCols matrix))
  else
    panic! "ValueError: shape() expects a rectangular matrix"

/-- Build a zero-filled matrix. -/
def pyNumpyZeros (shape : Int × Int) : List (List Float) :=
  let rows' := pyNumpyNatFromInt shape.1
  let cols' := pyNumpyNatFromInt shape.2
  List.replicate rows' (List.replicate cols' 0.0)

/-- Build a one-filled matrix. -/
def pyNumpyOnes (shape : Int × Int) : List (List Float) :=
  let rows' := pyNumpyNatFromInt shape.1
  let cols' := pyNumpyNatFromInt shape.2
  List.replicate rows' (List.replicate cols' 1.0)

/-- Build an identity matrix. -/
def pyNumpyEye (n : Int) : List (List Float) :=
  let n' := pyNumpyNatFromInt n
  (List.range n').map (fun i =>
    (List.range n').map (fun j => if i = j then 1.0 else 0.0))

/-- Transpose a rectangular matrix. -/
def pyNumpyTranspose {α} [PyNumpyScalar α] (matrix : List (List α)) : List (List Float) :=
  if pyNumpyIsRectangular matrix then
    let normalized := pyNumpyArray matrix
    (List.range (pyNumpyCols matrix)).map (fun c =>
      normalized.map (fun row => row.getD c 0.0))
  else
    panic! "ValueError: transpose() expects a rectangular matrix"

/-- Element-wise binary matrix operation. -/
def pyNumpyBinaryMatrix
    {α β : Type} [PyNumpyScalar α] [PyNumpyScalar β]
    (f : Float -> Float -> Float)
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  if pyNumpyIsRectangular lhs && pyNumpyIsRectangular rhs && pyNumpySameShape? lhs rhs then
    List.zipWith (fun lrow rrow =>
      List.zipWith f (lrow.map toFloat) (rrow.map toFloat)) lhs rhs
  else
    panic! "ValueError: matrices must have the same rectangular shape"

/-- Add two matrices element-wise. -/
def pyNumpyAdd {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  pyNumpyBinaryMatrix (· + ·) lhs rhs

/-- Subtract two matrices element-wise. -/
def pyNumpySubtract {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  pyNumpyBinaryMatrix (· - ·) lhs rhs

/-- Multiply two matrices element-wise. -/
def pyNumpyMultiply {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  pyNumpyBinaryMatrix (· * ·) lhs rhs

/-- Scale every element in a matrix by a scalar. -/
def pyNumpyScale {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (scalar : α) (matrix : List (List β)) : List (List Float) :=
  if pyNumpyIsRectangular matrix then
    let s := toFloat scalar
    (pyNumpyArray matrix).map (fun row => row.map (fun x => s * x))
  else
    panic! "ValueError: scale() expects a rectangular matrix"

/-- Dot product of two vectors. -/
def pyNumpyDotFloats : List Float -> List Float -> Float
  | [], [] => 0.0
  | x :: xs, y :: ys => x * y + pyNumpyDotFloats xs ys
  | _, _ => panic! "ValueError: dot() expects vectors of the same length"

/-- Dot product of two vectors, converting entries to `Float`. -/
def pyNumpyDot {α β} [PyNumpyScalar α] [PyNumpyScalar β] (lhs : List α) (rhs : List β) : Float :=
  if lhs.length = rhs.length then
    pyNumpyDotFloats (lhs.map toFloat) (rhs.map toFloat)
  else
    panic! "ValueError: dot() expects vectors of the same length"

/-- Matrix multiplication. -/
def pyNumpyMatmul {α β} [PyNumpyScalar α] [PyNumpyScalar β]
    (lhs : List (List α)) (rhs : List (List β)) : List (List Float) :=
  if pyNumpyIsRectangular lhs && pyNumpyIsRectangular rhs && pyNumpyCols lhs = pyNumpyRows rhs then
    let lhsF := pyNumpyArray lhs
    let rhsT := pyNumpyTranspose rhs
    lhsF.map (fun row => rhsT.map (fun col => pyNumpyDotFloats row col))
  else
    panic! "ValueError: matmul() requires compatible rectangular matrices"

/-- Sum all entries in a matrix. -/
def pyNumpySum {α} [PyNumpyScalar α] (matrix : List (List α)) : Float :=
  (pyNumpyArray matrix).flatten.foldl (· + ·) 0.0

/-- Mean of all entries in a matrix. -/
def pyNumpyMean {α} [PyNumpyScalar α] (matrix : List (List α)) : Float :=
  let entries := (pyNumpyArray matrix).flatten
  if entries.isEmpty then
    panic! "ValueError: mean() of an empty matrix is undefined"
  else
    entries.foldl (· + ·) 0.0 / Rat.toFloat (entries.length : Rat)

/-- Trace of a square matrix. -/
def pyNumpyTrace {α} [PyNumpyScalar α] (matrix : List (List α)) : Float :=
  if pyNumpyIsSquare matrix then
    let normalized := pyNumpyArray matrix
    (List.range normalized.length).foldl
      (fun acc i => acc + (normalized.getD i []).getD i 0.0)
      0.0
  else
    panic! "ValueError: trace() expects a square matrix"

/-- Flatten a matrix into a vector. -/
def pyNumpyFlatten {α} [PyNumpyScalar α] (matrix : List (List α)) : List Float :=
  (pyNumpyArray matrix).flatten

end Libraries.numpy
