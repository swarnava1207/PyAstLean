import Mathlib
import Libraries.scipy.ScipyDef

namespace Libraries.scipy

/-- Library-local registry for Python's `scipy` members (flattened across its submodules
`special` / `constants` / `stats` / `linalg`). -/
def pythonScipyMemberMap? (member : String) : Option Lean.Name :=
  match member with
  -- scipy.constants
  | "pi" => some ``pyScipyPi
  | "golden" => some ``pyScipyGolden
  | "golden_ratio" => some ``pyScipyGolden
  -- scipy.special
  | "factorial" => some ``pyScipyFactorial
  | "comb" => some ``pyScipyComb
  | "perm" => some ``pyScipyPerm
  | "gamma" => some ``pyScipyGamma
  | "erf" => some ``pyScipyErf
  -- scipy.stats
  | "tmean" => some ``pyScipyTmean
  | "gmean" => some ``pyScipyGmean
  | "hmean" => some ``pyScipyHmean
  -- scipy.linalg
  | "norm" => some ``pyScipyNorm
  | "det" => some ``pyScipyDet
  | _ => none

end Libraries.scipy
