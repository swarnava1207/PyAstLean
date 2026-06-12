import Mathlib
import PyAstLean.PyAPI.Core

namespace PyAstLean

universe u v

/--
Python-style value formatting used by the printing runtime.

This is intentionally separate from Lean's `ToString` / `Repr` so we can make common
runtime values look more like Python when printed.
-/
class PyPrintable (α : Type u) where
  pyStringify : α → String

export PyPrintable (pyStringify)

/--
One printable argument in a Python-style `print(...)` call.

This wrapper lets Lean accept heterogeneous argument lists like
`["sum", (3 : Int), true]` while still routing each element through the
`PyPrintable` typeclass.
-/
structure PyPrintArg where
  rendered : String

/-- Any printable Lean value can be used directly as a Python print argument. -/
instance {α : Type u} [PyPrintable α] : CoeOut α PyPrintArg where
  coe x := ⟨pyStringify x⟩

/--
Wrap one printable value as a `print(...)` argument (the lowercase smart constructor for
`PyPrintArg`).

Generated `print(...)` code emits `pyPrintArg x` per argument — far tidier than the explicit
`PyPrintArg.mk (pyStringify x)` it replaces — while still applying `pyStringify` eagerly, so each
argument elaborates at its own type before the heterogeneous `List PyPrintArg` is assembled (the
reason codegen can't just lean on the `CoeOut` coercion, which would force `PyPrintArg` onto
polymorphic argument terms).
-/
@[inline] def pyPrintArg {α : Type u} [PyPrintable α] (x : α) : PyPrintArg :=
  ⟨pyStringify x⟩

/-- Join already-formatted pieces with the separator Python's `print` commonly uses. -/
private def pyJoinPrinted (parts : List String) : String :=
  String.intercalate ", " parts

/-- Render a Python-style `print(...)` call from already-formatted argument strings. -/
def pyPrintRendered (parts : List String) (sep : String := " ") (ending : String := "\n") : String :=
  String.intercalate sep parts ++ ending

/-- Render a Python-style `print(...)` call from heterogeneous printable arguments. -/
def pyPrintArgsRendered (parts : List PyPrintArg) (sep : String := " ") (ending : String := "\n") : String :=
  pyPrintRendered (parts.map PyPrintArg.rendered) sep ending

/-- Strings print as themselves, without Lean quotes. -/
instance : PyPrintable String where
  pyStringify s := s

/-- Booleans use Python casing. -/
instance : PyPrintable Bool where
  pyStringify b := if b then "True" else "False"

/-- Lean's unit values line up with Python `None` when printed. -/
instance : PyPrintable Unit where
  pyStringify _ := "None"

/-- Lean's pretty-printed `PUnit` also behaves like Python `None`. -/
instance : PyPrintable PUnit where
  pyStringify _ := "None"

/-- Characters print as one-character strings. -/
instance : PyPrintable Char where
  pyStringify c := String.singleton c

/-- Numeric values can use Lean's ordinary string form. -/
instance : PyPrintable Int where
  pyStringify n := toString n

instance : PyPrintable Nat where
  pyStringify n := toString n

instance : PyPrintable Rat where
  pyStringify q := toString q

/-- Python exceptions print with their existing `ToString` rendering. -/
instance : PyPrintable PyException where
  pyStringify exc := toString exc

/-- `None` stays visible; present values print as the value itself. -/
instance [PyPrintable α] : PyPrintable (Option α) where
  pyStringify
    | none => "None"
    | some value => pyStringify value

/-- Lists print with Python-style brackets and comma separation. -/
instance [PyPrintable α] : PyPrintable (List α) where
  pyStringify xs :=
    "[" ++ pyJoinPrinted (xs.map pyStringify) ++ "]"

/-- Pairs print as Python tuples. Larger tuples still show as nested pairs for now. -/
instance [PyPrintable α] [PyPrintable β] : PyPrintable (α × β) where
  pyStringify p :=
    "(" ++ pyStringify p.1 ++ ", " ++ pyStringify p.2 ++ ")"

/--
Hash maps print as Python-style dictionaries.

The underlying runtime type does not preserve Python insertion order, so we sort by
the printed key to keep the rendered output deterministic in tests.
-/
instance [PyPrintable α] [PyPrintable β] [BEq α] [Hashable α] :
    PyPrintable (Std.HashMap α β) where
  pyStringify m :=
    let rendered :=
      m.toList.map fun (k, v) =>
        let keyText := pyStringify k
        (keyText, keyText ++ ": " ++ pyStringify v)
    let sorted := rendered.mergeSort (fun a b => compare a.1 b.1 != Ordering.gt)
    "{" ++ pyJoinPrinted (sorted.map Prod.snd) ++ "}"

/-- Function values do not have a good runtime textual form, so use a Python-style placeholder. -/
instance {α : Type u} {β : Type v} : PyPrintable (α → β) where
  pyStringify _ := "<function>"

/--
Fallback printer for any value that already has a `Repr`.

This keeps the printing surface extensible without forcing every new runtime type to
add a custom `PyPrintable` instance on day one.
-/
@[default_instance low]
instance [Repr α] : PyPrintable α where
  pyStringify x := reprStr x

/-- Public helper returning the Python-style printable text for a value. -/
def pyPrintStr {α : Type u} [PyPrintable α] (x : α) : String :=
  pyStringify x

/--
Real console-printing helper using Python-style `print(...)` semantics.

The input is a heterogeneous list of printable arguments, so both single-value and
multi-value calls go through the same user-facing API:

`pyPrintIO ["sum", (3 : Int), true]`
-/
def pyPrintIO (parts : List PyPrintArg) (sep : String := " ") (ending : String := "\n") : IO Unit :=
  IO.print (pyPrintArgsRendered parts sep ending)

/--
Pure compatibility surface mirroring `pyPrintIO`.

This preserves Python formatting semantics without attempting visible console output
inside non-`IO` translated code paths.
-/
def pyPrint (parts : List PyPrintArg) (sep : String := " ") (ending : String := "\n") : Unit :=
  let _ := pyPrintArgsRendered parts sep ending
  ()

end PyAstLean
