import LowRank.WishartLowerProbability

/-! The dimension-uniform lower query-complexity rate with no remaining
Wishart spectral-probability assumption. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem rectangularQueryComplexity_rate {p : ℝ} (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤
        rectangularQueryComplexity.{u} a b k p ε δ := by
  obtain ⟨c, hc, hmain⟩ := rectangularQueryComplexity_rate_of_wishart_lower_tail.{u}
    hp (by norm_num : (0 : ℝ) < 1 / 1000000)
  refine ⟨c, hc, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ
  apply hmain a b k ε δ hk hkN hε hε1 hδ
  intro d _ hdk
  apply gaussianMatrixLaw_wishart_lower_tail hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  exact_mod_cast (show (k : ℝ) < d by linarith)

end
end LowRank
