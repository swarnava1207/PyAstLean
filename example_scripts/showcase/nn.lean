import PyAstLean
import Libraries

open PyAstLean
open Libraries

def sigmoid := fun (x : Float) ↦ (1.0 : Float) /ₚ ((1.0 : Float) +ₚ Libraries.math.pyMathExp (-x))

def predict := fun (x : List Float) ↦ fun (w1 : List (List Float)) ↦ fun (b1 : List Float) ↦
  fun (w2 : List (List Float)) ↦ fun (b2 : List Float) ↦
  -- Forward pass through a 2 -> 2 -> 1 network.
  let h0 :=
    sigmoid (Libraries.numpy.pyNumpyDot x (PyAstLean.pyGetItem w1 (0 : Int)) +ₚ PyAstLean.pyGetItem b1 (0 : Int))
  let h1 :=
    sigmoid (Libraries.numpy.pyNumpyDot x (PyAstLean.pyGetItem w1 (1 : Int)) +ₚ PyAstLean.pyGetItem b1 (1 : Int))
  let hidden := [h0, h1]
  sigmoid (Libraries.numpy.pyNumpyDot hidden (PyAstLean.pyGetItem w2 (0 : Int)) +ₚ PyAstLean.pyGetItem b2 (0 : Int))

def mean_squared_error := fun (xs : List (List Float)) ↦ fun (ys : List Float) ↦ fun (w1 : List (List Float)) ↦
  fun (b1 : List Float) ↦ fun (w2 : List (List Float)) ↦ fun (b2 : List Float) ↦
  Id.run
    (do
      let mut total := (0.0 : Float)
      for i in (PyAstLean.pyRange (PyAstLean.pyLen xs))do
        let mut diff := predict (PyAstLean.pyGetItem xs i) w1 b1 w2 b2 -ₚ PyAstLean.pyGetItem ys i
        total := total +ₚ diff *ₚ diff
      let __py_ret := total /ₚ PyAstLean.pyLen xs
      return __py_ret)

def main' :=
  ((do
      -- XOR is not linearly separable, so a single layer cannot solve it -- the
      -- hidden layer is what makes this learnable.
      let mut xs :=
        [[(0.0 : Float), (0.0 : Float)], [(0.0 : Float), (1.0 : Float)], [(1.0 : Float), (0.0 : Float)],
          [(1.0 : Float), (1.0 : Float)]]
      let mut ys := [(0.0 : Float), (1.0 : Float), (1.0 : Float), (0.0 : Float)]
      -- Fixed initial weights so the run is reproducible (no RNG needed).
      let mut w1 := [[(0.5 : Float), -(0.4 : Float)], [(0.9 : Float), (1.0 : Float)]]
      let mut b1 := [(0.1 : Float), -(0.2 : Float)]
      let mut w2 := [[(0.7 : Float), -(0.8 : Float)]]
      let mut b2 := [(0.3 : Float)]
      let mut lr := (0.5 : Float)
      let mut epochs := (4000 : Int)
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.PyPrintArg.mk
                (PyAstLean.PyPrintable.pyStringify "=== Training a neural net on XOR (NumPy + math) ===")]
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.PyPrintArg.mk
                (PyAstLean.PyPrintable.pyStringify s! "initial loss: {mean_squared_error xs ys w1 b1 w2 b2}")]
      for epoch in (PyAstLean.pyRange epochs)do
        for i in (PyAstLean.pyRange (PyAstLean.pyLen xs))do
          let mut x := PyAstLean.pyGetItem xs i
          let mut y := PyAstLean.pyGetItem ys i
          -- Forward pass, keeping the hidden activations for backprop.
          let mut h0 :=
            sigmoid
              (Libraries.numpy.pyNumpyDot x (PyAstLean.pyGetItem w1 (0 : Int)) +ₚ PyAstLean.pyGetItem b1 (0 : Int))
          let mut h1 :=
            sigmoid
              (Libraries.numpy.pyNumpyDot x (PyAstLean.pyGetItem w1 (1 : Int)) +ₚ PyAstLean.pyGetItem b1 (1 : Int))
          let mut hidden := [h0, h1]
          let mut out :=
            sigmoid
              (Libraries.numpy.pyNumpyDot hidden (PyAstLean.pyGetItem w2 (0 : Int)) +ₚ PyAstLean.pyGetItem b2 (0 : Int))
          -- Backward pass: gradients of 1/2 the squared error.
          let mut d_out := ((out -ₚ y) *ₚ out) *ₚ ((1.0 : Float) -ₚ out)
          let mut d_h0 :=
            ((d_out *ₚ PyAstLean.pyGetItem (PyAstLean.pyGetItem w2 (0 : Int)) (0 : Int)) *ₚ h0) *ₚ ((1.0 : Float) -ₚ h0)
          let mut d_h1 :=
            ((d_out *ₚ PyAstLean.pyGetItem (PyAstLean.pyGetItem w2 (0 : Int)) (1 : Int)) *ₚ h1) *ₚ ((1.0 : Float) -ₚ h1)
          -- Gradient-descent step (rebuild each weight row in place).
          w2 :=
            PyAstLean.pySetItem w2 (0 : Int)
              [PyAstLean.pyGetItem (PyAstLean.pyGetItem w2 (0 : Int)) (0 : Int) -ₚ (lr *ₚ d_out) *ₚ h0,
                PyAstLean.pyGetItem (PyAstLean.pyGetItem w2 (0 : Int)) (1 : Int) -ₚ (lr *ₚ d_out) *ₚ h1]
          b2 := [PyAstLean.pyGetItem b2 (0 : Int) -ₚ lr *ₚ d_out]
          w1 :=
            PyAstLean.pySetItem w1 (0 : Int)
              [PyAstLean.pyGetItem (PyAstLean.pyGetItem w1 (0 : Int)) (0 : Int) -ₚ
                  (lr *ₚ d_h0) *ₚ PyAstLean.pyGetItem x (0 : Int),
                PyAstLean.pyGetItem (PyAstLean.pyGetItem w1 (0 : Int)) (1 : Int) -ₚ
                  (lr *ₚ d_h0) *ₚ PyAstLean.pyGetItem x (1 : Int)]
          w1 :=
            PyAstLean.pySetItem w1 (1 : Int)
              [PyAstLean.pyGetItem (PyAstLean.pyGetItem w1 (1 : Int)) (0 : Int) -ₚ
                  (lr *ₚ d_h1) *ₚ PyAstLean.pyGetItem x (0 : Int),
                PyAstLean.pyGetItem (PyAstLean.pyGetItem w1 (1 : Int)) (1 : Int) -ₚ
                  (lr *ₚ d_h1) *ₚ PyAstLean.pyGetItem x (1 : Int)]
          b1 := [PyAstLean.pyGetItem b1 (0 : Int) -ₚ lr *ₚ d_h0, PyAstLean.pyGetItem b1 (1 : Int) -ₚ lr *ₚ d_h1]
        if (epoch +ₚ (1 : Int)) %ₚ (1000 : Int) == (0 : Int) then
          let _ ←
            PyAstLean.pyPrintIO
                [PyAstLean.PyPrintArg.mk
                    (PyAstLean.PyPrintable.pyStringify
                      s!"epoch {(epoch +ₚ (1 : Int))}: loss = {mean_squared_error xs ys w1 b1 w2 b2}")]
        else
          let _ := ()
      let _ ← PyAstLean.pyPrintIO [PyAstLean.PyPrintArg.mk (PyAstLean.PyPrintable.pyStringify "learned predictions:")]
      for i in (PyAstLean.pyRange (PyAstLean.pyLen xs))do
        let mut p := predict (PyAstLean.pyGetItem xs i) w1 b1 w2 b2
        let mut label := if decide (p > (0.5 : Float)) then (1 : Int) else (0 : Int)
        let _ ←
          PyAstLean.pyPrintIO
              [PyAstLean.PyPrintArg.mk
                  (PyAstLean.PyPrintable.pyStringify
                    s!"  {(PyAstLean.pyGetItem xs
                        i)} -> {p }  (class {label }, target {PyAstLean.pyInt (PyAstLean.pyGetItem ys i)})")]) :
    IO _)

def main : IO Unit := do
  let _ ← main'
  pure ()

/--
info: === Training a neural net on XOR (NumPy + math) ===
initial loss: 0.255404
epoch 1000: loss = 0.174257
epoch 2000: loss = 0.003965
epoch 3000: loss = 0.001645
epoch 4000: loss = 0.001019
learned predictions:
  [0.000000, 0.000000] -> 0.031944  (class 0, target 0)
  [0.000000, 1.000000] -> 0.962974  (class 1, target 1)
  [1.000000, 0.000000] -> 0.970558  (class 1, target 1)
  [1.000000, 1.000000] -> 0.028602  (class 0, target 0)
-/
#guard_msgs in
#eval main
