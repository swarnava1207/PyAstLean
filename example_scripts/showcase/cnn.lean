import PyAstLean
import Libraries

open PyAstLean
open Libraries

structure CNN where
  kernel : List (List Float)
  dense_w : List Float
  dense_b : Float
  deriving Inhabited, Repr

deriving instance BEq for CNN

def CNN.new : CNN :=
  Id.run
    (do
      let mut self : CNN := default
      -- Explicit annotations pin the Lean structure field types.
      self := { self with kernel := [[(0.1 : Float), -(0.2 : Float)], [(0.15 : Float), (0.05 : Float)]] }
      self := { self with dense_w := [(0.1 : Float), -(0.1 : Float), (0.2 : Float), -(0.2 : Float)] }
      self := { self with dense_b := (0.0 : Float) }
      return self)

def CNN.sigmoid := fun (self : CNN) ↦ fun (x : Float) ↦
  (1.0 : Float) /ₚ ((1.0 : Float) +ₚ Libraries.math.pyMathExp (-x))

def CNN.conv := fun (self : CNN) ↦ fun (img : List (List Float)) ↦
  Id.run
    (do
      -- Valid 2x2 convolution over a 3x3 image -> 2x2 feature map.
      let mut out := []
      for i in (PyAstLean.pyRange (2 : Int))do
        let mut row := []
        for j in (PyAstLean.pyRange (2 : Int))do
          let mut s := (0.0 : Float)
          for a in (PyAstLean.pyRange (2 : Int))do
            for b in (PyAstLean.pyRange (2 : Int))do
              s := s +ₚ img⦋i +ₚ a⦌⦋j +ₚ b⦌ *ₚ self.kernel⦋a⦌⦋b⦌
          row := PyAstLean.pyAppend row s
        out := PyAstLean.pyAppend out row
      return out)

def CNN.relu2d := fun (self : CNN) ↦ fun (fm : List (List Float)) ↦
  Id.run
    (do
      let mut out := []
      for i in (PyAstLean.pyRange (2 : Int))do
        let mut row := []
        for j in (PyAstLean.pyRange (2 : Int))do
          let mut v := fm⦋i⦌⦋j⦌
          if decide (v < (0.0 : Float)) then 
            v := (0.0 : Float)
          else
            let _ := ()
          row := PyAstLean.pyAppend row v
        out := PyAstLean.pyAppend out row
      return out)

def CNN.flatten := fun (self : CNN) ↦ fun (fm : List (List Float)) ↦
  [fm⦋(0 : Int)⦌⦋(0 : Int)⦌, fm⦋(0 : Int)⦌⦋(1 : Int)⦌, fm⦋(1 : Int)⦌⦋(0 : Int)⦌, fm⦋(1 : Int)⦌⦋(1 : Int)⦌]

def CNN.forward := fun (self : CNN) ↦ fun (img : List (List Float)) ↦
  Id.run
    (do
      let mut c := CNN.conv self img
      let mut r := CNN.relu2d self c
      let mut f := CNN.flatten self r
      let mut z := self.dense_b
      for k in (PyAstLean.pyRange (4 : Int))do
        z := z +ₚ f⦋k⦌ *ₚ self.dense_w⦋k⦌
      let __py_ret := CNN.sigmoid self z
      return __py_ret)

def CNN.predict := fun (self : CNN) ↦ fun (img : List (List Float)) ↦
  Id.run
    (do
      if decide (CNN.forward self img ≥ (0.5 : Float)) then 
        return (1 : Int)
      else
        let _ := ()
      return (0 : Int))

def CNN.train := fun (self : CNN) ↦ fun (images : List (List (List Float))) ↦ fun (labels : List Int) ↦
  fun (epochs : Int) ↦ fun (lr : Float) ↦
  Id.run
    (do
      let mut self := self
      -- Stochastic gradient descent with binary cross-entropy (the sigmoid+BCE gradient on the
      -- logit reduces to `pred - target`). Each step rebuilds the parameter lists rather than
      -- mutating them in place, matching the transpiler's value-semantics model.
      for e in (PyAstLean.pyRange epochs)do
        for n in (PyAstLean.pyRange (PyAstLean.pyLen images))do
          let mut img := images⦋n⦌
          let mut target := PyAstLean.pyFloat labels⦋n⦌
          -- Forward pass, keeping the intermediates we need for backprop.
          let mut c := CNN.conv self img
          let mut r := CNN.relu2d self c
          let mut f := CNN.flatten self r
          let mut z := self.dense_b
          for k in (PyAstLean.pyRange (4 : Int))do
            z := z +ₚ f⦋k⦌ *ₚ self.dense_w⦋k⦌
          let mut pred := CNN.sigmoid self z
          let mut d_logit := pred -ₚ target
          -- Gradient w.r.t. the flattened features (uses the pre-update dense weights).
          let mut dflat := []
          for k in (PyAstLean.pyRange (4 : Int))do
            dflat := PyAstLean.pyAppend dflat (d_logit *ₚ self.dense_w⦋k⦌)
          -- Update the dense layer.
          let mut new_w := []
          for k in (PyAstLean.pyRange (4 : Int))do
            new_w := PyAstLean.pyAppend new_w (self.dense_w⦋k⦌ -ₚ (lr *ₚ d_logit) *ₚ f⦋k⦌)
          self := { self with dense_w := new_w }
          self := { self with dense_b := self.dense_b -ₚ lr *ₚ d_logit }
          -- Backprop through ReLU, reshaping the 4-vector grad to the 2x2 map.
          let mut dconv := [[(0.0 : Float), (0.0 : Float)], [(0.0 : Float), (0.0 : Float)]]
          let mut idx := (0 : Int)
          for i in (PyAstLean.pyRange (2 : Int))do
            for j in (PyAstLean.pyRange (2 : Int))do
              let mut g := dflat⦋idx⦌
              if decide (r⦋i⦌⦋j⦌ ≤ (0.0 : Float)) then 
                g := (0.0 : Float)
              else
                let _ := ()
              dconv := PyAstLean.pySetItem dconv i (PyAstLean.pySetItem dconv⦋i⦌ j g)
              idx := idx +ₚ (1 : Int)
          -- Backprop into the convolution kernel and update it.
          let mut new_kernel := [[(0.0 : Float), (0.0 : Float)], [(0.0 : Float), (0.0 : Float)]]
          for a in (PyAstLean.pyRange (2 : Int))do
            for b in (PyAstLean.pyRange (2 : Int))do
              let mut gk := (0.0 : Float)
              for i in (PyAstLean.pyRange (2 : Int))do
                for j in (PyAstLean.pyRange (2 : Int))do
                  gk := gk +ₚ dconv⦋i⦌⦋j⦌ *ₚ img⦋i +ₚ a⦌⦋j +ₚ b⦌
              new_kernel :=
                PyAstLean.pySetItem new_kernel a (PyAstLean.pySetItem new_kernel⦋a⦌ b (self.kernel⦋a⦌⦋b⦌ -ₚ lr *ₚ gk))
          self := { self with kernel := new_kernel }
      return self)

def main' :=
  ((do
      -- Vertical-stripe images are class 1; horizontal-stripe images are class 0.
      let mut images :=
        [[[(1.0 : Float), (0.0 : Float), (0.0 : Float)], [(1.0 : Float), (0.0 : Float), (0.0 : Float)],
            [(1.0 : Float), (0.0 : Float), (0.0 : Float)]],
          [[(0.0 : Float), (1.0 : Float), (0.0 : Float)], [(0.0 : Float), (1.0 : Float), (0.0 : Float)],
            [(0.0 : Float), (1.0 : Float), (0.0 : Float)]],
          [[(0.0 : Float), (0.0 : Float), (1.0 : Float)], [(0.0 : Float), (0.0 : Float), (1.0 : Float)],
            [(0.0 : Float), (0.0 : Float), (1.0 : Float)]],
          [[(1.0 : Float), (1.0 : Float), (1.0 : Float)], [(0.0 : Float), (0.0 : Float), (0.0 : Float)],
            [(0.0 : Float), (0.0 : Float), (0.0 : Float)]],
          [[(0.0 : Float), (0.0 : Float), (0.0 : Float)], [(1.0 : Float), (1.0 : Float), (1.0 : Float)],
            [(0.0 : Float), (0.0 : Float), (0.0 : Float)]],
          [[(0.0 : Float), (0.0 : Float), (0.0 : Float)], [(0.0 : Float), (0.0 : Float), (0.0 : Float)],
            [(1.0 : Float), (1.0 : Float), (1.0 : Float)]]]
      let mut labels := [(1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)]
      let mut cnn := CNN.new
      cnn := CNN.train cnn images labels (400 : Int) (0.5 : Float)
      let mut correct := (0 : Int)
      for n in (PyAstLean.pyRange (PyAstLean.pyLen images))do
        if CNN.predict cnn images⦋n⦌ == labels⦋n⦌ then 
          correct := correct +ₚ (1 : Int)
        else
          let _ := ()
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.pyArg "accuracy:", PyAstLean.pyArg correct, PyAstLean.pyArg "/",
              PyAstLean.pyArg (PyAstLean.pyLen images)]
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.pyArg "vertical   sample -> class", PyAstLean.pyArg (CNN.predict cnn images⦋(0 : Int)⦌)]
      let _ ←
        PyAstLean.pyPrintIO
            [PyAstLean.pyArg "horizontal sample -> class", PyAstLean.pyArg (CNN.predict cnn images⦋(3 : Int)⦌)]) :
    IO _)

def main : IO Unit := do
  let _ ← main'
  pure ()
