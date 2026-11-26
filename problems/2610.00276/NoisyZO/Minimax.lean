import Mathlib.Order.CompleteLattice.Basic

/-!
# Order-theoretic minimax assembly

This file isolates the final `inf`--`sup` step in a form that is independent of
the analytic definition of the risk.  The codomain is an arbitrary complete
lattice, so in applications it can be instantiated with `ℝ≥0∞` without any
boundedness side condition.
-/

namespace NoisyZO

/-- The minimax value of a risk: first take the worst objective for each
algorithm, then the best algorithm. -/
def minimaxRisk {Algorithm Objective Risk : Type*} [CompleteLattice Risk]
    (risk : Algorithm → Objective → Risk) : Risk :=
  ⨅ algorithm, ⨆ objective, risk algorithm objective

/-- A single algorithm with a uniform risk bound gives a minimax upper bound. -/
theorem minimaxRisk_le_of_algorithm
    {Algorithm Objective Risk : Type*} [CompleteLattice Risk]
    (risk : Algorithm → Objective → Risk) (algorithm : Algorithm) (upper : Risk)
    (hupper : ∀ objective, risk algorithm objective ≤ upper) :
    minimaxRisk risk ≤ upper := by
  exact (iInf_le (fun a => ⨆ objective, risk a objective) algorithm).trans
    (iSup_le hupper)

/-- A hard objective for every algorithm gives a minimax lower bound. -/
theorem le_minimaxRisk_of_hard_instance
    {Algorithm Objective Risk : Type*} [CompleteLattice Risk]
    (risk : Algorithm → Objective → Risk) (lower : Risk)
    (hlower : ∀ algorithm, ∃ objective, lower ≤ risk algorithm objective) :
    lower ≤ minimaxRisk risk := by
  apply le_iInf
  intro algorithm
  obtain ⟨objective, hobjective⟩ := hlower algorithm
  exact hobjective.trans (le_iSup (risk algorithm) objective)

/-- The lower and upper proof obligations used in a sharp minimax theorem can
be discharged independently and joined without any further analytic premise. -/
theorem minimaxRisk_between
    {Algorithm Objective Risk : Type*} [CompleteLattice Risk]
    (risk : Algorithm → Objective → Risk) (lower upper : Risk)
    (hlower : ∀ algorithm, ∃ objective, lower ≤ risk algorithm objective)
    (algorithm : Algorithm)
    (hupper : ∀ objective, risk algorithm objective ≤ upper) :
    lower ≤ minimaxRisk risk ∧ minimaxRisk risk ≤ upper :=
  ⟨le_minimaxRisk_of_hard_instance risk lower hlower,
    minimaxRisk_le_of_algorithm risk algorithm upper hupper⟩

/-- If the two independently proved bounds have the same value, they identify
the minimax risk exactly. -/
theorem minimaxRisk_eq
    {Algorithm Objective Risk : Type*} [CompleteLattice Risk]
    (risk : Algorithm → Objective → Risk) (rate : Risk)
    (hlower : ∀ algorithm, ∃ objective, rate ≤ risk algorithm objective)
    (algorithm : Algorithm)
    (hupper : ∀ objective, risk algorithm objective ≤ rate) :
    minimaxRisk risk = rate := by
  exact le_antisymm
    (minimaxRisk_le_of_algorithm risk algorithm rate hupper)
    (le_minimaxRisk_of_hard_instance risk rate hlower)

end NoisyZO
