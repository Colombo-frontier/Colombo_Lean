import LowRank.GaussianRankHardness
import LowRank.RectangularQueryComplexity

/-! Zero-padding transports the unconditional Gaussian rank baseline to
rectangular column-output algorithms and their actual minimax complexity. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem exists_rectangular_rank_input_zero_success {a b d k n : ℕ}
    (ha : d ≤ a) (hb : d ≤ b) (hk : k < d) (hn : n < k)
    {p ε : ℝ} (hp : 0 < p) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S) :
    ∃ W : Matrix (Fin d) (Fin d) ℝ, W.PosSemidef ∧ W.rank = k ∧
      ν.real (rectangularSchattenSuccess p ε policy (zeroPadFin ha hb W)) = 0 := by
  let L := coordinateEmbedding ha
  let R := coordinateEmbedding hb
  obtain ⟨W, hW, hrank, hzero⟩ := exists_fixed_rank_input_zero_success hk hn (ε := ε) hp ν
    (reduceRectangularColumnPolicy L R n policy)
    (reduceRectangularColumnPolicy_outputs hk.le L R n policy)
  refine ⟨W, hW, hrank, le_antisymm ?_ (measureReal_nonneg)⟩
  exact (reduceRectangularColumnPolicy_probability hk.le hp L (coordinateEmbedding_orthogonal ha)
    R (coordinateEmbedding_orthogonal hb) n ν policy W).trans_eq hzero

theorem RectangularColumnAlgorithm.rank_le_budget {a b k n : ℕ} {p ε δ : ℝ}
    (alg : RectangularColumnAlgorithm.{u} a b k n) (hk : k < min a b)
    (hp : 0 < p) (hδ : 0 < δ) (hs : alg.Succeeds p ε δ) : k ≤ n := by
  by_contra! hn
  obtain ⟨W, _, _, hzero⟩ := exists_rectangular_rank_input_zero_success
    (Nat.min_le_left a b) (Nat.min_le_right a b) hk hn hp alg.law alg.policy
  have hsuccess := hs (zeroPadFin (Nat.min_le_left a b) (Nat.min_le_right a b) W)
  rw [hzero] at hsuccess
  exact (not_le_of_gt hδ) hsuccess

theorem rectangularQueryComplexity_rank_baseline {a b k : ℕ} {p ε δ : ℝ}
    (hk : k < min a b) (hp : 0 < p) (hδ : 0 < δ) :
    (k : ℝ≥0∞) ≤ rectangularQueryComplexity.{u} a b k p ε δ := by
  rw [← ENNReal.ofReal_natCast]
  apply le_rectangularQueryComplexity
  intro n alg hs
  exact_mod_cast alg.rank_le_budget hk hp hδ hs

end
end LowRank
