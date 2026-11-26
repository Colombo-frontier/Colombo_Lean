import NoisyZO.LowerAlgorithmOutput
import NoisyZO.Minimax
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.ENNReal.Inv

/-!
# From the hypercube average to a minimax hard instance

The Assouad lower chain produces an average over all Boolean vertices.  This
module extracts one hard vertex for every algorithm and feeds that statement
directly into the complete-lattice minimax wrapper.
-/

open scoped BigOperators ENNReal

namespace NoisyZO

noncomputable section

/-- A lower bound on the uniform hypercube average is attained as a lower
bound by at least one vertex. -/
theorem exists_hypercube_risk_ge_average
    {d : ℕ} (risk : Hypercube d → ℝ) (lower : ℝ)
    (hlower : lower ≤ (∑ s : Hypercube d, risk s) / (2 : ℝ) ^ d) :
    ∃ s : Hypercube d, lower ≤ risk s := by
  have havg : lower ≤ 𝔼 s : Hypercube d, risk s := by
    rw [Fintype.expect_eq_sum_div_card]
    simpa using hlower
  obtain ⟨s, _hs, hs⟩ := Finset.exists_le_of_le_expect
    (s := (Finset.univ : Finset (Hypercube d))) Finset.univ_nonempty havg
  exact ⟨s, hs⟩

/-- Real average lower bounds lift monotonically to an `ENNReal` hard
instance, the codomain used by the minimax wrapper. -/
theorem exists_hypercube_ennreal_risk_ge_average
    {d : ℕ} (risk : Hypercube d → ℝ) (lower : ℝ)
    (hlower : lower ≤ (∑ s : Hypercube d, risk s) / (2 : ℝ) ^ d) :
    ∃ s : Hypercube d, ENNReal.ofReal lower ≤ ENNReal.ofReal (risk s) := by
  obtain ⟨s, hs⟩ := exists_hypercube_risk_ge_average risk lower hlower
  exact ⟨s, ENNReal.ofReal_le_ofReal hs⟩

/-- If every algorithm satisfies the Assouad hypercube-average lower bound,
then the corresponding `ENNReal` minimax risk satisfies the same bound. -/
theorem ofReal_le_minimaxRisk_of_average_hypercube
    {Algorithm : Type*} {d : ℕ}
    (risk : Algorithm → Hypercube d → ℝ) (lower : ℝ)
    (hlower : ∀ algorithm,
      lower ≤ (∑ s : Hypercube d, risk algorithm s) / (2 : ℝ) ^ d) :
    ENNReal.ofReal lower ≤
      minimaxRisk (fun algorithm s ↦ ENNReal.ofReal (risk algorithm s)) := by
  apply le_minimaxRisk_of_hard_instance
  intro algorithm
  exact exists_hypercube_ennreal_risk_ge_average
    (risk algorithm) lower (hlower algorithm)

end

end NoisyZO
