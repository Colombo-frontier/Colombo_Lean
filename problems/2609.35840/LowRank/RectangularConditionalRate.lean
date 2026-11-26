import LowRank.RectangularRankBaseline
import LowRank.RectangularNonsaturatedRate

/-! Combine both rank regimes for the actual rectangular minimax model.
The only remaining lower-bound premise is the uniform Wishart spectral
probability estimate stated explicitly in this theorem. -/

namespace LowRank
open Matrix MeasureTheory
open scoped ENNReal
noncomputable section
universe u

theorem rectangularQueryComplexity_rate_of_wishart_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ →
      (∀ d : ℕ, d ≤ min a b → 100 * (k : ℝ) ≤ (d : ℝ) →
        (gaussianMatrixLaw d (d - k)).real (wishartSpectralEvent d (d - k) L c₀ k)ᶜ ≤ 1 / 20) →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤
        rectangularQueryComplexity.{u} a b k p ε δ := by
  obtain ⟨η, hη, _, hlarge⟩ :=
    rectangularQueryComplexity_nonsaturated_of_wishart_probability.{u} hp hL hc
  refine ⟨η / 202, by positivity, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ hprob
  have hR := (targetRate_pos (hk.trans hkN) hk hε).le
  have hprod := mul_nonneg hη.le hR
  by_cases hregime : 202 * (k : ℝ) < η * targetRate (min a b) k ε
  · have hbound := hlarge a b k ε δ hk hε hε1 hδ hregime hprob
    exact (ENNReal.ofReal_le_ofReal (by linarith :
      (η / 202) * targetRate (min a b) k ε ≤ η * targetRate (min a b) k ε / 200)).trans hbound
  · have hsmall : (η / 202) * targetRate (min a b) k ε ≤ (k : ℝ) := by
      push_neg at hregime
      linarith
    have hbase := rectangularQueryComplexity_rank_baseline.{u} (ε := ε) hkN hp
      (show 0 < δ by linarith)
    have hbound := ENNReal.ofReal_le_ofReal hsmall
    rw [ENNReal.ofReal_natCast] at hbound
    exact hbound.trans hbase

end
end LowRank
