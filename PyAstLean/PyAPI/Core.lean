import Mathlib

namespace PyAstLean

/-- Minimal runtime value for translated Python exceptions. -/
structure PyException where
  kind : String
  msg : String
  deriving Inhabited, Repr, BEq

namespace PyException

/-- Smart constructor used by codegen so generated Lean does not need to expose `.mk`. -/
def Raise (kind : String) (msg : String := "") : PyException :=
  .mk kind msg

/-- Accessor used by generated code when matching caught exceptions by kind. -/
def OfKind (exc : PyException) : String :=
  exc.kind

end PyException

/-- Concrete exception monad used for translated Python code that can raise. -/
abbrev PyExcept (α : Type) := ExceptT PyException IO α

instance : ToString PyException where
  toString exc :=
    if exc.msg.isEmpty then
      exc.kind
    else
      s!"{exc.kind}: {exc.msg}"

/-- Python-style `range` supporting positive and negative steps. -/
def pyRange (stop : Int) (start : Int := 0) (step : Int := 1) : List Int := do
  if step > 0 then
    List.map (fun i => start + i) (List.range' 0 ((stop - start) / step + (stop - start) % step).toNat step.toNat)
  else if step < 0 then
    List.map (fun i => start - i) (List.range' 0 ((start - stop) / (-step) + (start - stop) % (-step)).toNat (-step).toNat)
  else
    []

/-- Python-style list indexing with negative indices and runtime failure on out-of-bounds access. -/
def pyListGetItem {α : Type} [Inhabited α] (xs : List α) (idx : Int) : α :=
  let len := xs.length
  if len == 0 then
    panic! "IndexError: list index out of range"
  else
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      panic! "IndexError: list index out of range"
    else
      match xs[trueIdx.toNat]? with
      | some value => value
      | none => panic! "IndexError: list index out of range"

/-- Python-style slicing for lists. -/
def pyListSlice {α : Type} (xs : List α) (start : Option Int) (stop : Option Int) : List α :=
  let len := xs.length
  let start : Nat := match start with
    | some i => if i < 0 then (max 0 (len + i)).toNat else (min len i.toNat)
    | none => 0
  let stop : Nat := match stop with
    | some i => if i < 0 then (max 0 (len + i)).toNat else (min len i.toNat)
    | none => len
  xs.take stop |> List.drop start

/-- Python-style indexing/slicing for strings. -/
def pyStringGetItem (s : String) (idx : Int) : Option Char :=
  let lst := s.toList
  let len := lst.length
  if len == 0 then
    none
  else
    let lenInt : Int := len
    let trueIdx := if idx < 0 then lenInt + idx else idx
    if trueIdx < 0 || trueIdx >= lenInt then
      none
    else
      lst[trueIdx.toNat]?

/-- Python-style slicing for strings. -/
def pyStringSlice (s : String) (start : Option Int) (stop : Option Int) : String :=
  let lst := s.toList
  let sliced := pyListSlice lst start stop
  String.ofList sliced

end PyAstLean
