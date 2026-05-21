-- This file is for testing the outputs

import PyAstLean.PyGens
import PyAstLean.PyGens.Basic
namespace PyAstLean

def sqrt_demo := fun x ↦ Libraries.math.pyMathSqrt x

def read_line : IO String := do
  let mut raw ← PyAstLean.pyInputIO ""
  return raw

def read_prompted : IO String := do
  return ((← PyAstLean.pyInputIO "n = "))

def read_nested_int :=
  ((do
      let mut a ←
        ((do
              let __py_input0 ← PyAstLean.pyInputIO "Enter a: "
              return PyAstLean.pyInt __py_input0) :
            IO _)
      let mut b ←
        ((do
              let __py_input0 ← PyAstLean.pyInputIO "Enter b: "
              return PyAstLean.pyInt __py_input0) :
            IO _)
      let mut c ← PyAstLean.pyInputIO "Enter c: "
      a := a +ₚ b
      return ((a, c))) :
    IO _)

def echo_input : IO Int := do
  let _ ←
    ((do
          let __py_input0 ← PyAstLean.pyInputIO ""
          let __py_result ← PyAstLean.pyPrintIO [__py_input0]
          return __py_result) :
        IO _)
  return (0 : Int)

def input_inside_print :=
  ((do
      let _ ←
        ((do
              let __py_input0 ← PyAstLean.pyInputIO ""
              let __py_result ←
                PyAstLean.pyPrintIO
                    [String.append (String.append "" "Enter a number: ")
                        (ToString.toString (PyAstLean.pyInt __py_input0))]
              return __py_result) :
            IO _)) :
    IO _)

end PyAstLean

def main : IO Unit := do
  let x <- PyAstLean.read_nested_int
  IO.println s!"returned: {x}"
