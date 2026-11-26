import LowRank.CubicMinimaxUpper
import LowRank.RectangularLowerRate

/-! The two-sided minimax rate for the proved range 1 <= p <= 2.
The upper multiplier is the explicitly defined cubicQueryLogFactor. -/

namespace LowRank
open scoped ENNReal
noncomputable section
universe u

theorem rectangularQueryComplexity_two_sided_one_to_two {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ → δ ≤ 19 / 20 →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤ rectangularQueryComplexity.{u} a b k p ε δ ∧
      rectangularQueryComplexity.{u} a b k p ε δ ≤
        ENNReal.ofReal (cubicQueryLogFactor a k ε * targetRate (min a b) k ε) := by
  obtain ⟨c, hc, hlow⟩ := rectangularQueryComplexity_rate.{u} (by linarith : 0 < p)
  refine ⟨c, hc, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ hδ1
  exact ⟨hlow a b k ε δ hk hkN hε hε1 hδ,
    rectangularQueryComplexity_le_cubic_rate hk ((lt_min_iff.mp hkN).2.le) hp hp2 hε hε1 hδ1⟩

end
end LowRank
