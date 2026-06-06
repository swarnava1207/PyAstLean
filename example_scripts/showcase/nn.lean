import PyAstLean
import Libraries

open PyAstLean
open Libraries
def sigmoid := fun (x : Float) ↦ (1.0 : Float) /ₚ ((1.0 : Float) +ₚ Libraries.math.pyMathExp (-x))

def relu := fun (x : Float) ↦
  Id.run
    (do
      if decide (x > (0.0 : Float)) then
        return x
      else
        let _ := ()
      return (0.0 : Float))

def dense_layer := fun (inputs : List Float) ↦ fun (weights : List (List Float)) ↦ fun (biases : List Float) ↦
  Id.run
    (do
      -- A fully-connected layer: one neuron per row of `weights`.
      let mut outputs := []
      for j in (PyAstLean.pyRange (PyAstLean.pyLen weights))do
        let mut z := Libraries.numpy.pyNumpyDot inputs (PyAstLean.pyGetItem weights j) +ₚ PyAstLean.pyGetItem biases j
        outputs := PyAstLean.pyAppend outputs z
      return outputs)

def apply_sigmoid := fun (xs : List Float) ↦ List.map (fun x => sigmoid x) (PyAstLean.pyIter xs)

def apply_relu := fun (xs : List Float) ↦ List.map (fun x => relu x) (PyAstLean.pyIter xs)

def softmax := fun (xs : List Float) ↦
  -- Numerically-stable softmax: subtract the max before exponentiating.
  let m := PyAstLean.pyMax xs
  let exps := List.map (fun x => Libraries.math.pyMathExp (x -ₚ m)) (PyAstLean.pyIter xs)
  let total := PyAstLean.pySum exps
  List.map (fun e => e /ₚ total) (PyAstLean.pyIter exps)

def cross_entropy := fun (probs : List Float) ↦ fun target ↦
  -- Negative log-likelihood of the target class.
  -Libraries.math.pyMathLog (PyAstLean.pyGetItem probs target)

def forward := fun features ↦
  -- Hidden layer 1: 3 inputs -> 4 neurons, ReLU.
  let w1 :=
    [[(0.1 : Float), -(0.2 : Float), (0.3 : Float)], [(0.4 : Float), (0.5 : Float), -(0.1 : Float)],
      [-(0.3 : Float), (0.2 : Float), (0.1 : Float)], [(0.05 : Float), -(0.4 : Float), (0.25 : Float)]]
  let b1 := [(0.1 : Float), -(0.2 : Float), (0.05 : Float), (0.0 : Float)]
  -- Hidden layer 2: 4 inputs -> 3 neurons, sigmoid.
  let w2 :=
    [[(0.2 : Float), -(0.1 : Float), (0.4 : Float), (0.1 : Float)],
      [-(0.3 : Float), (0.3 : Float), (0.1 : Float), -(0.2 : Float)],
      [(0.1 : Float), (0.2 : Float), -(0.4 : Float), (0.3 : Float)]]
  let b2 := [(0.0 : Float), (0.1 : Float), -(0.1 : Float)]
  -- Output layer: 3 inputs -> 2 classes, softmax.
  let w3 := [[(0.5 : Float), -(0.2 : Float), (0.3 : Float)], [-(0.4 : Float), (0.6 : Float), (0.1 : Float)]]
  let b3 := [(0.05 : Float), -(0.05 : Float)]
  let h1 := apply_relu (dense_layer features w1 b1)
  let h2 := apply_sigmoid (dense_layer h1 w2 b2)
  let logits := dense_layer h2 w3 b3
  let probs := softmax logits
  probs

def main' :=
  ((do
      let mut dataset :=
        [[(0.5 : Float), -(0.2 : Float), (0.1 : Float)], [(0.9 : Float), (0.4 : Float), -(0.3 : Float)],
          [-(0.6 : Float), (0.2 : Float), (0.8 : Float)]]
      let mut targets := [(0 : Int), (1 : Int), (1 : Int)]
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.PyPrintArg.mk (PyAstLean.PyPrintable.pyStringify "=== Tiny Neural Network (NumPy + math) ===")]
      let mut total_loss := (0.0 : Float)
      let mut correct := (0 : Int)
      for i in (PyAstLean.pyRange (PyAstLean.pyLen dataset))do
        let mut features := PyAstLean.pyGetItem dataset i
        let mut probs := forward features
        let mut pred := Libraries.numpy.pyNumpyArgmax probs
        let mut loss := cross_entropy probs (PyAstLean.pyGetItem targets i)
        total_loss := total_loss +ₚ loss
        if pred == PyAstLean.pyGetItem targets i then
          correct := correct +ₚ (1 : Int)
        else
          let _ := ()
        let _ ←
          PyAstLean.pyPrintIO
              [PyAstLean.PyPrintArg.mk
                  (PyAstLean.PyPrintable.pyStringify
                    (String.append
                      (String.append
                        (String.append
                          (String.append
                            (String.append
                              (String.append
                                (String.append
                                  (String.append (String.append (String.append "" "sample ") (ToString.toString i))
                                    ": probs=")
                                  (ToString.toString probs))
                                " pred=")
                              (ToString.toString pred))
                            " target=")
                          (ToString.toString (PyAstLean.pyGetItem targets i)))
                        " loss=")
                      (ToString.toString loss)))]
      let mut avg_loss := total_loss /ₚ PyAstLean.pyLen dataset
      let mut accuracy := correct /ₚ PyAstLean.pyLen dataset
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.PyPrintArg.mk
                (PyAstLean.PyPrintable.pyStringify
                  (String.append (String.append "" "average loss: ") (ToString.toString avg_loss)))]
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.PyPrintArg.mk
                (PyAstLean.PyPrintable.pyStringify
                  (String.append (String.append "" "accuracy: ") (ToString.toString accuracy)))]) :
    IO _)

def main : IO Unit := do
  let _ ← main'
  pure ()

#eval main
