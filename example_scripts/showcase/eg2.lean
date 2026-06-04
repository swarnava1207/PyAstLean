import PyAstLean
import Libraries

open PyAstLean
open Libraries

def process_data := fun (data : List (List Float)) ↦ fun (weights : List (List Float)) ↦
  ((do
      try
        do
          -- Calculate mean of the dataset
          let mut m := Libraries.numpy.pyNumpyMean data
          let _ ← PyAstLean.pyPrintIO [String.append (String.append "" "Dataset Global Mean: ") (ToString.toString m)]
          -- Center the data by subtracting the mean
          -- (Using a manual broadcast-like subtraction for this example)
          -- Note: np.subtract is mapped to pyNumpySubtract
          let mut centered := Libraries.numpy.pyNumpySubtract data [[m, m], [m, m]]
          -- Perform matrix multiplication
          -- Note: np.matmul is mapped to pyNumpyMatmul
          let mut result := Libraries.numpy.pyNumpyMatmul centered weights
          return result
      catch caught =>
        if (caught).OfKind == "ValueError" then
          do
            let e := caught
            let _ ← PyAstLean.pyPrintIO [String.append (String.append "" "Processing failed: ") (ToString.toString e)]
            -- Fallback to a zero matrix if dimensions fail
            return (Libraries.numpy.pyNumpyZeros ((2 : Int), (2 : Int)))
        else
          throw caught) :
    PyAstLean.PyExcept _)

def run_example :=
  ((do
      -- Define a 2x2 dataset and a 2x2 weight matrix
      let mut dataset :=
        [[Float.ofScientific 10 true 1, Float.ofScientific 20 true 1],
          [Float.ofScientific 30 true 1, Float.ofScientific 40 true 1]]
      let mut weights :=
        [[Float.ofScientific 5 true 1, Float.ofScientific 5 true 1],
          [Float.ofScientific 10 true 1, Float.ofScientific 20 true 1]]
      let _ ← PyAstLean.pyPrintIO ["=== PyAstLean NumPy Showcase ==="]
      let _ ← PyAstLean.pyPrintIO [String.append (String.append "" "Input Data: ") (ToString.toString dataset)]
      let _ ← PyAstLean.pyPrintIO [String.append (String.append "" "Weight Matrix: ") (ToString.toString weights)]
      -- 1. Main Processing Pipeline
      let _ ← PyAstLean.pyPrintIO ["\n[1] Running Data Pipeline:"]
      let mut output := (← process_data dataset weights)
      let _ ← PyAstLean.pyPrintIO [String.append (String.append "" "Final Result:\n") (ToString.toString output)]
      -- 2. Utility Operations
      let _ ← PyAstLean.pyPrintIO ["\n[2] Structural Operations:"]
      let _ ←
        PyAstLean.pyPrintIO
            [String.append (String.append "" "Identity Matrix (2x2):\n")
                (ToString.toString (Libraries.numpy.pyNumpyEye (2 : Int)))]
      let _ ←
        PyAstLean.pyPrintIO
            [String.append (String.append "" "Flattened Weights: ")
                (ToString.toString (Libraries.numpy.pyNumpyFlatten weights))]
      -- 3. Shape Info
      -- Note: np.shape returns (rows, cols)
      let (rows, cols) := Libraries.numpy.pyNumpyShape dataset
      let _ ←
        PyAstLean.pyPrintIO
            [String.append
                (String.append (String.append (String.append "" "Dataset Shape: ") (ToString.toString rows)) "x")
                (ToString.toString cols)]
      -- 4. Error Handling Simulation
      let _ ← PyAstLean.pyPrintIO ["\n[3] Exception Handling (Mismatched Dimensions):"]
      let mut invalid_data :=
        [[Float.ofScientific 10 true 1, Float.ofScientific 20 true 1, Float.ofScientific 30 true 1]]
      -- This should trigger the ValueError in np.matmul(1x3, 2x2)
      let _ ← process_data invalid_data weights) :
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

/-
Lean Answer:

=== PyAstLean NumPy Showcase ===
Input Data: [[1.000000, 2.000000], [3.000000, 4.000000]]
Weight Matrix: [[0.500000, 0.500000], [1.000000, 2.000000]]

[1] Running Data Pipeline:
Dataset Global Mean: 2.500000
Final Result:
[[-1.250000, -1.750000], [1.750000, 3.250000]]

[2] Structural Operations:
Identity Matrix (2x2):
[[1.000000, 0.000000], [0.000000, 1.000000]]
Flattened Weights: [0.500000, 0.500000, 1.000000, 2.000000]
Dataset Shape: 2x2

[3] Exception Handling (Mismatched Dimensions):
Dataset Global Mean: 2.000000


---

Python Answer:

=== PyAstLean NumPy Showcase ===
Input Data: [[1.0, 2.0], [3.0, 4.0]]
Weight Matrix: [[0.5, 0.5], [1.0, 2.0]]

[1] Running Data Pipeline:
Dataset Global Mean: 2.5
Final Result:
[[-1.25 -1.75]
 [ 1.75  3.25]]

[2] Structural Operations:
Identity Matrix (2x2):
[[1. 0.]
 [0. 1.]]
Flattened Weights: [0.5 0.5 1.  2. ]
Dataset Shape: 2x2

[3] Exception Handling (Mismatched Dimensions):
Dataset Global Mean: 2.0
Processing failed: operands could not be broadcast together with shapes (1,3) (2,2)
-/
