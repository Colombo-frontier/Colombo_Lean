import LowRank.RectangularQueryComplexity
import LowRank.RateArithmetic

/-! The actual minimax complexity satisfies the target rate in the large
hard-dimension regime, conditional on the stated Wishart probability
estimate. All dimension rounding and cubic smallness are discharged here. -/

namespace LowRank
open Matrix MeasureTheory
open scoped ENNReal
noncomputable section
universe u

theorem exists_cubic_dimension_fraction {C : ℝ} (hC : 0 < C) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ C * η ^ 3 ≤ 1 / 4 := by
  let η := min 1 (1 / (4 * C))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηC : η ≤ 1 / (4 * C) := min_le_right _ _
  have hmul : η * (4 * C) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hηC
  have hpow : η ^ 3 ≤ η := by
    have h := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 2) hη.le hη1) hη.le
    nlinarith
  refine ⟨η, hη, hη1, ?_⟩
  calc
    C * η ^ 3 ≤ C * η := mul_le_mul_of_nonneg_left hpow hC.le
    _ ≤ 1 / 4 := by nlinarith

theorem rectangularQueryComplexity_nonsaturated_of_wishart_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ →
      202 * (k : ℝ) < η * targetRate (min a b) k ε →
      (∀ d : ℕ, d ≤ min a b → 100 * (k : ℝ) ≤ (d : ℝ) →
        (gaussianMatrixLaw d (d - k)).real (wishartSpectralEvent d (d - k) L c₀ k)ᶜ ≤ 1 / 20) →
      ENNReal.ofReal (η * targetRate (min a b) k ε / 200) ≤
        rectangularQueryComplexity.{u} a b k p ε δ := by
  obtain ⟨C, hC, hmain⟩ := rectangularQueryComplexity_lower_of_wishart_probability.{u} hp hL hc
  obtain ⟨η, hη, hη1, hηC⟩ := exists_cubic_dimension_fraction hC
  refine ⟨η, hη, hη1, ?_⟩
  intro a b k ε δ hk hε hε1 hδ hlarge hprob
  obtain ⟨d, hdN, hkd, hdaccuracy, hrate⟩ :=
    hard_dimension_exists (Nat.succ_le_iff.mpr hk) hε hη hη1 hlarge
  have hsmall : C * ε * (d : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 := by
    calc
      _ = C * (ε * (d : ℝ) ^ 3) := by ring
      _ ≤ C * (η ^ 3 * (k : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left (dimension_implies_cubic_smallness hε (Nat.cast_nonneg d) hdaccuracy) hC.le
      _ = (C * η ^ 3) * (k : ℝ) ^ 3 := by ring
      _ ≤ (1 / 4) * (k : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hηC (by positivity)
      _ = _ := by ring
  have hcost := hmain a b d k ε δ (hdN.trans (Nat.min_le_left a b))
    (hdN.trans (Nat.min_le_right a b)) hk hε.le hε1 hδ (by linarith) hsmall (hprob d hdN hkd)
  exact (ENNReal.ofReal_le_ofReal (by linarith :
    η * targetRate (min a b) k ε / 200 ≤ (d : ℝ) / 100)).trans hcost

end
end LowRank
