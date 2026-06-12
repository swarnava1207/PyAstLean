import Mathlib

namespace Libraries.scipy

/-!
Python `scipy` runtime surface (a Mathlib-only, **computable** subset).

`scipy` leans heavily on transcendental functions whose Mathlib counterparts (`Real.Gamma`,
`Real.pi`, ...) are `noncomputable`, so generated Lean could not `#eval`/run them. We therefore
model the numeric core directly on Lean `Float`: exact combinatorics via `Nat.factorial` /
`Nat.choose`, and standard self-contained approximations (Lanczos for `gamma`,
Abramowitz–Stegun for `erf`). Everything here stays executable.
-/

/-- Types acceptable to the float-oriented `scipy` surface (mirrors the `math` shim). -/
class PyScipyFloatArg (α : Type) where
  toFloat : α → Float

export PyScipyFloatArg (toFloat)

instance : PyScipyFloatArg Float where toFloat := id
instance : PyScipyFloatArg Rat where toFloat := Rat.toFloat
instance : PyScipyFloatArg Int where toFloat x := Rat.toFloat (x : Rat)
instance : PyScipyFloatArg Nat where toFloat x := Rat.toFloat (x : Rat)
instance : PyScipyFloatArg Bool where toFloat b := if b then 1.0 else 0.0

/-- Sum a list of floats (no `List.sum` specialisation needed downstream). -/
private def fsum (xs : List Float) : Float :=
  xs.foldl (· + ·) 0.0

/-! ## scipy.constants -/

/-- `scipy.constants.pi`. -/
def pyScipyPi : Float := 3.141592653589793

/-- `scipy.constants.golden` / `golden_ratio` (the golden ratio φ). -/
def pyScipyGolden : Float := 1.618033988749895

/-! ## scipy.special -/

/-- `scipy.special.factorial` — exact via `Nat.factorial`, returned as a float (scipy default).
Negative inputs yield `0` as in scipy. -/
def pyScipyFactorial (n : Int) : Float :=
  if n < 0 then 0.0 else Float.ofNat (Nat.factorial n.toNat)

/-- `scipy.special.comb` — binomial coefficient C(n, k), exact via `Nat.choose`. -/
def pyScipyComb (n k : Int) : Float :=
  if n < 0 || k < 0 then 0.0 else Float.ofNat (Nat.choose n.toNat k.toNat)

/-- `scipy.special.perm` — number of permutations P(n, k), exact via `Nat.descFactorial`. -/
def pyScipyPerm (n k : Int) : Float :=
  if n < 0 || k < 0 then 0.0 else Float.ofNat (Nat.descFactorial n.toNat k.toNat)

/-- Lanczos coefficients (g = 7), highest-quality double-precision set. -/
private def lanczosG : Float := 7.0
private def lanczosC : List Float :=
  [ 0.99999999999980993, 676.5203681218851, -1259.1392167224028,
    771.32342877765313, -176.61502916214059, 12.507343278686905,
    -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7 ]

/-- Computable `scipy.special.gamma` via the Lanczos approximation (with the reflection
formula for the left half-plane). -/
partial def gammaFloat (x : Float) : Float :=
  if x < 0.5 then
    -- reflection: Γ(x)·Γ(1-x) = π / sin(πx)
    pyScipyPi / (Float.sin (pyScipyPi * x) * gammaFloat (1.0 - x))
  else
    let x := x - 1.0
    let a := lanczosC.headD 0.0
    let rest := lanczosC.tail
    -- a₀ + Σ cᵢ/(x+i)  for i = 1..8
    let a := (rest.zipIdx).foldl (init := a) (fun acc (c, i) =>
      acc + c / (x + Float.ofNat (i + 1)))
    let t := x + lanczosG + 0.5
    Float.sqrt (2.0 * pyScipyPi) * Float.exp ((x + 0.5) * Float.log t - t) * a

def pyScipyGamma {α : Type} [PyScipyFloatArg α] (x : α) : Float :=
  gammaFloat (toFloat x)

/-- Computable `scipy.special.erf` via the Abramowitz–Stegun 7.1.26 approximation
(|error| ≤ 1.5e-7). -/
def erfFloat (x : Float) : Float :=
  let sign := if x < 0.0 then -1.0 else 1.0
  let z := Float.abs x
  let t := 1.0 / (1.0 + 0.3275911 * z)
  let poly := ((((1.061405429 * t - 1.453152027) * t + 1.421413741) * t
                - 0.284496736) * t + 0.254829592) * t
  let y := 1.0 - poly * Float.exp (-z * z)
  sign * y

def pyScipyErf {α : Type} [PyScipyFloatArg α] (x : α) : Float :=
  erfFloat (toFloat x)

/-! ## scipy.stats -/

/-- `scipy.stats.tmean` with no trimming limits — the arithmetic mean. -/
def pyScipyTmean (xs : List Float) : Float :=
  if xs.isEmpty then 0.0 else fsum xs / Float.ofNat xs.length

/-- `scipy.stats.gmean` — geometric mean `exp(mean(log xs))`. -/
def pyScipyGmean (xs : List Float) : Float :=
  if xs.isEmpty then 0.0 else Float.exp (fsum (xs.map Float.log) / Float.ofNat xs.length)

/-- `scipy.stats.hmean` — harmonic mean `n / Σ(1/xᵢ)`. -/
def pyScipyHmean (xs : List Float) : Float :=
  if xs.isEmpty then 0.0 else Float.ofNat xs.length / fsum (xs.map (fun x => 1.0 / x))

/-! ## scipy.linalg -/

/-- `scipy.linalg.norm`, overloaded over vectors and matrices (Frobenius for matrices). -/
class ScipyNormable (α : Type) where
  scipyNorm : α → Float

instance : ScipyNormable (List Float) where
  scipyNorm xs := Float.sqrt (fsum (xs.map (fun x => x * x)))

instance : ScipyNormable (List (List Float)) where
  scipyNorm m := Float.sqrt (fsum (m.map (fun row => fsum (row.map (fun x => x * x)))))

def pyScipyNorm {α : Type} [ScipyNormable α] (x : α) : Float :=
  ScipyNormable.scipyNorm x

/-- `scipy.linalg.det` via Laplace (cofactor) expansion along the first row. Exact on `Float`;
fine for the small matrices generated code typically builds. -/
partial def pyScipyDet (m : List (List Float)) : Float :=
  match m with
  | [] => 1.0
  | [row] => row.headD 0.0
  | first :: _ =>
    let n := m.length
    (List.range n).foldl (init := 0.0) (fun acc j =>
      let minor := (m.drop 1).map (fun row => row.eraseIdx j)
      let sign := if j % 2 == 0 then 1.0 else -1.0
      acc + sign * (first.getD j 0.0) * pyScipyDet minor)

end Libraries.scipy
