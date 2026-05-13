import Lean
open Lean

def hello := "world"

namespace PyAstLean

def pyPrint {α : Type} [ToString α] (_ : α) : Unit := ()

end PyAstLean
