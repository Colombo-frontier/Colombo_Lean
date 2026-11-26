import LowRank.ConvertedPairedKrylovAlgorithm
import LowRank.CubicTwoSidedRate

/-! Choose the shorter matrix dimension for the paired construction.
Converting the opposite orientation costs k queries, absorbed in the rate. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

def cubicConvertedQueryBudget (b k : ℕ) (ε : ℝ) : ℕ :=
  pairedKrylovContinuationBudget (2 * k + 2) (2 * wideKrylovRank k ε + 2) (0 + k)
    (chebyshevFilterDegree (cubicKrylovGap ε) (cubicNarrowTolerance b k ε) + 1)
    (chebyshevFilterDegree 1 (cubicWideTolerance b k ε) + 1)

theorem cubicConvertedQueryBudget_eq (b k : ℕ) (ε : ℝ) :
    cubicConvertedQueryBudget b k ε = k + cubicPairedQueryBudget b k ε := by
  unfold cubicConvertedQueryBudget cubicPairedQueryBudget
  rw [pairedKrylovContinuationBudget_eq, pairedKrylovQueryBudget_eq]
  omega

def cubicConvertedAlgorithm (a b k : ℕ) (ε : ℝ) (hka : k ≤ a) (hkb : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (cubicConvertedQueryBudget b k ε) :=
  convertedPairedKrylovAlgorithm a b k (2 * k + 2) (2 * wideKrylovRank k ε + 2)
    (chebyshevFilterDegree (cubicKrylovGap ε) (cubicNarrowTolerance b k ε) + 1)
    (chebyshevFilterDegree 1 (cubicWideTolerance b k ε) + 1) hka hkb

theorem cubicConvertedAlgorithm_succeeds {a b k : ℕ} (hk0 : 0 < k)
    (hka : k ≤ a) (hkb : k ≤ b) {p ε δ : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ ≤ 19 / 20) (hfit : wideKrylovRank k ε < b) :
    (cubicConvertedAlgorithm.{u} a b k ε hka hkb).Succeeds p ε δ := by
  intro A
  exact hδ.trans ((refinedPairedKrylovAlgorithm_cubic_success hk0 hka Aᵀ hp hp2 hε hε1 hfit).trans
    (convertedPairedKrylovAlgorithm_success_probability_ge hka hkb (by linarith : 0 < p) A))

def minimumDimensionLogFactor (N k : ℕ) (ε : ℝ) : ℝ := cubicQueryLogFactor N k ε + 1

theorem minimumDimensionLogFactor_ge {N k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) : 73 ≤ minimumDimensionLogFactor N k ε := by
  have h := cubicQueryLogFactor_ge (a := N) hk hε hε1
  unfold minimumDimensionLogFactor
  linarith

theorem cubicConvertedQueryBudget_le {b k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (cubicConvertedQueryBudget b k ε : ℝ) ≤ (k : ℝ) * accuracyScale ε * minimumDimensionLogFactor b k ε := by
  rw [cubicConvertedQueryBudget_eq, Nat.cast_add]
  have h := cubicPairedQueryBudget_le (a := b) hk hε hε1
  have hkScale : (k : ℝ) ≤ (k : ℝ) * accuracyScale ε :=
    le_mul_of_one_le_right (Nat.cast_nonneg k) (accuracyScale_ge_one hε hε1)
  unfold minimumDimensionLogFactor
  nlinarith

theorem rectangularQueryComplexity_le_minimum_dimension_log {a b k : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal ((k : ℝ) * accuracyScale ε * minimumDimensionLogFactor (min a b) k ε) := by
  have hks : 0 ≤ (k : ℝ) * accuracyScale ε := mul_nonneg (Nat.cast_nonneg k) (accuracyScale_pos hε).le
  by_cases hab : a ≤ b
  · rw [Nat.min_eq_left hab]
    apply (rectangularQueryComplexity_le_cubic_log hk0 hkb hp hp2 hε hε1 hδ).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (by unfold minimumDimensionLogFactor; linarith) hks
  · rw [Nat.min_eq_right (le_of_not_ge hab)]
    by_cases hfit : wideKrylovRank k ε < b
    · have hbudget := rectangularQueryComplexity_le_budget (cubicConvertedAlgorithm.{u} a b k ε hka hkb)
        (cubicConvertedAlgorithm_succeeds hk0 hka hkb hp hp2 hε hε1 hδ hfit)
      apply hbudget.trans
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal
        (cubicConvertedQueryBudget_le (b := b) hk0 hε hε1)
    · have hdim := rectangularQueryComplexity_le_dimension.{u} (a := a) hkb (by linarith : 0 < p)
        hε.le (by linarith : δ ≤ 1)
      rw [Nat.min_eq_right (le_of_not_ge hab)] at hdim
      have hb : (b : ℝ) ≤ (wideKrylovRank k ε : ℝ) := by exact_mod_cast (le_of_not_gt hfit)
      have hw := wideKrylovRank_le hk0 hε hε1
      have hf := minimumDimensionLogFactor_ge (N := b) hk0 hε hε1
      have hbound : (b : ℝ) ≤ (k : ℝ) * accuracyScale ε * minimumDimensionLogFactor b k ε := by
        calc
          _ ≤ 6 * ((k : ℝ) * accuracyScale ε) := hb.trans hw
          _ ≤ _ := by nlinarith
      apply hdim.trans
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound

theorem rectangularQueryComplexity_le_minimum_dimension_rate {a b k : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal (minimumDimensionLogFactor (min a b) k ε * targetRate (min a b) k ε) := by
  have hf := minimumDimensionLogFactor_ge (N := min a b) hk0 hε hε1
  by_cases hmin : ((min a b : ℕ) : ℝ) ≤ (k : ℝ) * accuracyScale ε
  · unfold targetRate
    rw [min_eq_left hmin]
    have hdim := rectangularQueryComplexity_le_dimension.{u} (a := a) hkb (by linarith : 0 < p)
      hε.le (by linarith : δ ≤ 1)
    apply hdim.trans
    have hbound : ((min a b : ℕ) : ℝ) ≤ minimumDimensionLogFactor (min a b) k ε * ((min a b : ℕ) : ℝ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith : 1 ≤ minimumDimensionLogFactor (min a b) k ε)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound
  · unfold targetRate
    rw [min_eq_right (le_of_not_ge hmin)]
    simpa only [mul_comm] using
      rectangularQueryComplexity_le_minimum_dimension_log.{u} hk0 hka hkb hp hp2 hε hε1 hδ

theorem rectangularQueryComplexity_two_sided_minimum_dimension {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a b k : ℕ) (ε δ : ℝ),
      0 < k → k < min a b → 0 < ε → ε ≤ 1 → 1 / 5 ≤ δ → δ ≤ 19 / 20 →
      ENNReal.ofReal (c * targetRate (min a b) k ε) ≤ rectangularQueryComplexity.{u} a b k p ε δ ∧
      rectangularQueryComplexity.{u} a b k p ε δ ≤
        ENNReal.ofReal (minimumDimensionLogFactor (min a b) k ε * targetRate (min a b) k ε) := by
  obtain ⟨c, hc, hlow⟩ := rectangularQueryComplexity_rate.{u} (by linarith : 0 < p)
  refine ⟨c, hc, ?_⟩
  intro a b k ε δ hk hkN hε hε1 hδ hδ1
  exact ⟨hlow a b k ε δ hk hkN hε hε1 hδ,
    rectangularQueryComplexity_le_minimum_dimension_rate hk (lt_min_iff.mp hkN).1.le
      (lt_min_iff.mp hkN).2.le hp hp2 hε hε1 hδ1⟩

end
end LowRank
