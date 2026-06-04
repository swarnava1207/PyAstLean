import PyAstLean
import Libraries

open PyAstLean
open Libraries

def euclidean_distance : List Int → List Int → PyAstLean.PyExcept Float := fun (p1 : List Int) ↦
  fun (p2 : List Int) ↦ do
  if pyLen p1 != pyLen p2 then
    throw
        (PyAstLean.PyException.Raise "ValueError" (ToString.toString "Points must have the same number of dimensions"))
  else
    let _ := ()
  -- Using zip, list comprehension, and math.pow
  let mut sq_diffs :=
    List.map
      (fun _pair =>
        let (a, b) := _pair;
        Libraries.math.pyMathPow (a -ₚ b) (2 : Int))
      (pyZip p1 p2)
  return (Libraries.math.pyMathSqrt (pySum sq_diffs))

def find_nearest_neighbor := fun (target : List Int) ↦ fun (dataset : List (List Int)) ↦
  ((do
      try
        do
          -- Calculate distances using list comprehension
          let mut distances := (← List.mapM (fun point => euclidean_distance target point) dataset)
          -- Find the minimum distance
          let mut min_dist := pyMin distances
          -- Find the index of the minimum distance
          -- Using a loop since index() might not be supported based on tests
          let mut min_index := -(1 : Int)
          for _pair in pyEnumerate distances do
            let (i, d) := _pair
            if d == min_dist then
              min_index := i
              break
            else
              let _ := ()
          return ((min_dist, PyAstLean.pyListGetItem dataset min_index))
      catch caught =>
        if (caught).OfKind == "ValueError" then
          do
            let e := caught
            let _ ←
              PyAstLean.pyPrintIO
                  [String.append (String.append "" "Error calculating distances: ") (ToString.toString e)]
            return ((-Float.ofScientific 10 true 1, []))
        else
          throw caught) :
    PyAstLean.PyExcept _)

def run_example :=
  ((do
      let mut dataset :=
        [[(1 : Int), (2 : Int), (3 : Int)], [(4 : Int), (5 : Int), (6 : Int)], [(7 : Int), (8 : Int), (9 : Int)],
          [(2 : Int), (1 : Int), (4 : Int)]]
      let mut target_point := [(2 : Int), (3 : Int), (4 : Int)]
      let mut invalid_point := [(1 : Int), (2 : Int)]
      let _ ← PyAstLean.pyPrintIO ["Dataset:", dataset]
      let _ ← PyAstLean.pyPrintIO ["Target Point:", target_point]
      -- Valid Case
      let (dist, nearest) ← find_nearest_neighbor target_point dataset
      let _ ← PyAstLean.pyPrintIO ["Nearest Neighbor to Target:"]
      let _ ← PyAstLean.pyPrintIO ["Point:", nearest]
      let _ ← PyAstLean.pyPrintIO ["Distance:", dist]
      -- Invalid Case
      let _ ← PyAstLean.pyPrintIO ["\nTesting Invalid Point:"]
      let (dist_inv, nearest_inv) ← find_nearest_neighbor invalid_point dataset
      let _ ← PyAstLean.pyPrintIO ["Fallback Distance:", dist_inv]) :
    PyAstLean.PyExcept _)

def main : IO Unit := do
  let result ←
    (((do
            let _ ← run_example
            pure ()) :
          PyAstLean.PyExcept Unit)).run
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

/--
info: Dataset: [[1, 2, 3], [4, 5, 6], [7, 8, 9], [2, 1, 4]]
Target Point: [2, 3, 4]
Nearest Neighbor to Target:
Point: [1, 2, 3]
Distance: 1.732051

Testing Invalid Point:
Error calculating distances: ValueError: Points must have the same number of dimensions
Fallback Distance: -1.000000
-/
#guard_msgs in
#eval main
/-
Python answer:

Dataset: [[1, 2, 3], [4, 5, 6], [7, 8, 9], [2, 1, 4]]
Target Point: [2, 3, 4]
Nearest Neighbor to Target:
Point: [1, 2, 3]
Distance: 1.7320508075688772

Testing Invalid Point:
Error calculating distances: Points must have the same number of dimensions
Fallback Distance: -1.0
-/
