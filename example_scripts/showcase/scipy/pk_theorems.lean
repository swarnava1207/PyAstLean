import Mathlib

/-!
# Provable invariants of the PK model in `pk_model.py`

The transpiler runs the two-compartment pharmacokinetic model on `Float`. Here we mirror the
*same* rate equations over `ℝ` and prove the pharmacologically meaningful properties that a
correct model must satisfy — the kind of facts a regulator or modeller actually cares about:

* **mass balance** — the system never creates or destroys drug except by elimination;
* **distribution is reversible** — the tissue exchange conserves mass;
* **per-step accounting** — one integrator step loses exactly the eliminated amount (no leak);
* **depot drains** — between doses the gut compartment is non-increasing.

Compartments (mg):  `depot` (gut)  →  `central` (plasma)  ⇄  `periph` (tissue);  rate
constants `ka, ke, k12, k21 ≥ 0` (1/h).
-/

namespace PKModel

variable (ka ke k12 k21 : ℝ)

/-- `dD/dt` — drug leaving the gut depot by first-order absorption. -/
def depotRate (depot : ℝ) : ℝ := -ka * depot

/-- `dC/dt` — absorption in, elimination out, reversible exchange with the tissue compartment. -/
def centralRate (depot central periph : ℝ) : ℝ :=
  ka * depot - ke * central - k12 * central + k21 * periph

/-- `dP/dt` — distribution into and back out of the tissue compartment. -/
def periphRate (central periph : ℝ) : ℝ := k12 * central - k21 * periph

/--
**Mass balance.** The total rate of change of drug across the whole system equals exactly the
elimination flux `-ke · C`. Absorption (`ka`) and distribution (`k12`, `k21`) only *move* drug
between compartments — they never create or destroy it. This is the single most important
sanity property of any compartmental PK model.
-/
theorem mass_balance (depot central periph : ℝ) :
    depotRate ka depot
      + centralRate ka ke k12 k21 depot central periph
      + periphRate k12 k21 central periph
    = -ke * central := by
  grind +locals

/--
**Distribution is mass-conserving.** The peripheral-exchange terms (`k12`/`k21`) contribute zero
net change to the combined plasma + tissue pool: whatever leaves plasma for tissue arrives in
tissue, and vice-versa.
-/
theorem distribution_conserves (central periph : ℝ) :
    (-k12 * central + k21 * periph) + (k12 * central - k21 * periph) = 0 := by
  ring

/--
**No elimination ⇒ total drug is conserved.** Setting `ke = 0` (a drug that is only
redistributed, never cleared) makes the total system rate identically zero.
-/
theorem conserved_without_elimination (depot central periph : ℝ) :
    depotRate ka depot
      + centralRate ka 0 k12 k21 depot central periph
      + periphRate k12 k21 central periph
    = 0 := by
  grind +locals

/-- One explicit forward-Euler step (exactly what `main` does each iteration in `pk_model.py`):
every compartment advances by its rate times the timestep `dt`. -/
def step (depot central periph dt : ℝ) : ℝ × ℝ × ℝ :=
  (depot   + depotRate ka depot * dt,
   central + centralRate ka ke k12 k21 depot central periph * dt,
   periph  + periphRate k12 k21 central periph * dt)

/--
**Per-step drug accounting.** After one Euler step the total drug in the system has dropped by
exactly the eliminated amount `ke · C · dt` — the discrete analogue of mass balance, and a proof
that the integrator itself introduces no spurious gain or loss of drug.
-/
theorem step_mass_balance (depot central periph dt : ℝ) :
    (step ka ke k12 k21 depot central periph dt).1
      + (step ka ke k12 k21 depot central periph dt).2.1
      + (step ka ke k12 k21 depot central periph dt).2.2
    = (depot + central + periph) - ke * central * dt := by
  grind +locals

/--
**The gut depot drains between doses.** With a non-negative absorption rate and a non-negative
amount left in the gut, `dD/dt ≤ 0`: absent a new dose, the depot only empties.
-/
theorem depot_nonincreasing (depot : ℝ) (hka : 0 ≤ ka) (hd : 0 ≤ depot) :
    depotRate ka depot ≤ 0 := by
  grind +locals [mul_nonneg hka hd]

/--
**Elimination is the only sink.** Combining mass balance with non-negativity: when plasma
concentration and the elimination rate are non-negative, the total system rate is `≤ 0` — drug
can only leave the body, never spontaneously appear.
-/
theorem total_nonincreasing (depot central periph : ℝ)
    (hke : 0 ≤ ke) (hc : 0 ≤ central) :
    depotRate ka depot
      + centralRate ka ke k12 k21 depot central periph
      + periphRate k12 k21 central periph
    ≤ 0 := by
  have h : 0 ≤ ke * central := mul_nonneg hke hc
  grind +locals

end PKModel
