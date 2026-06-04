import PyAstLean
import Std.Tactic.Do
import Libraries

open PyAstLean
open Libraries

open Std Do

set_option mvcgen.warning false

def euclidean_distance : List Int → List Int → PyAstLean.PyExcept Float := fun (p1 : List Int) ↦
  fun (p2 : List Int) ↦ do
  if h : pyLen p1 != pyLen p2 then
    throw
        (PyAstLean.PyException.Raise "ValueError" (ToString.toString "Points must have the same number of dimensions"))
  else
    let _ := ()

  have h : pyLen p1 = pyLen p2 := by
    simp [pyLen]
    apply Id.of_wp_run_eq
    · rfl
    · simp_all
      sorry
  -- Using zip, list comprehension, and math.pow
  let mut sq_diffs :=
    List.map
      (fun _pair =>
        let (a, b) := _pair;
        Libraries.math.pyMathPow (a -ₚ b) (2 : Int))
      (pyZip p1 p2)
  return (Libraries.math.pyMathSqrt (pySum sq_diffs))

def mySum (arr : Array Nat) : Nat := Id.run do
  let mut total := 0
  for x in arr do
    total := total + x
  return total

theorem mySum_correct (arr : Array Nat) : mySum arr = arr.sum := by
  generalize h : mySum arr = x
  apply Id.of_wp_run_eq h
  mvcgen
  · exact Classical.ofNonempty
  · sorry
  · simp_all [mySum]
    sorry
  · simp_all [mySum]
    sorry
