import LowRank.GeneralPairedKrylovBudget
import LowRank.ConvertedPairedKrylovAlgorithm
import LowRank.ExactRecoveryUpperBound
import LowRank.RectangularLowerRate

/-! Uniform minimax upper bounds for every finite p >= 1, in both matrix
orientations and including the exact-recovery dimension fallback. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

def generalPairedAlgorithm (p : ℝ) (a b k : ℕ) (ε : ℝ) (hka : k ≤ a) (hkb : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (generalPairedQueryBudget p a k ε) :=
  refinedPairedKrylovAlgorithm a b k (2 * k + 2) (2 * generalWideKrylovRank p k ε + 2)
    (generalNarrowRounds p a k ε) (generalWideRounds p a k ε) hka hkb

def generalConvertedQueryBudget (p : ℝ) (b k : ℕ) (ε : ℝ) : ℕ :=
  pairedKrylovContinuationBudget (2 * k + 2) (2 * generalWideKrylovRank p k ε + 2) (0 + k)
    (generalNarrowRounds p b k ε) (generalWideRounds p b k ε)

theorem generalConvertedQueryBudget_eq (p : ℝ) (b k : ℕ) (ε : ℝ) :
    generalConvertedQueryBudget p b k ε = k + generalPairedQueryBudget p b k ε := by
  unfold generalConvertedQueryBudget generalPairedQueryBudget
  rw [pairedKrylovContinuationBudget_eq, pairedKrylovQueryBudget_eq]
  omega

def generalConvertedAlgorithm (p : ℝ) (a b k : ℕ) (ε : ℝ) (hka : k ≤ a) (hkb : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (generalConvertedQueryBudget p b k ε) :=
  convertedPairedKrylovAlgorithm a b k (2 * k + 2) (2 * generalWideKrylovRank p k ε + 2)
    (generalNarrowRounds p b k ε) (generalWideRounds p b k ε) hka hkb

theorem generalPairedAlgorithm_succeeds {a b k : ℕ} (hk0 : 0 < k)
    (hka : k ≤ a) (hkb : k ≤ b) {p ε δ : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ ≤ 19 / 20) (hfit : generalWideKrylovRank p k ε < a) :
    (generalPairedAlgorithm.{u} p a b k ε hka hkb).Succeeds p ε δ := by
  intro A
  exact hδ.trans (refinedPairedKrylovAlgorithm_general_success hk0 hkb A hp hε hε1 hfit)

theorem generalConvertedAlgorithm_succeeds {a b k : ℕ} (hk0 : 0 < k)
    (hka : k ≤ a) (hkb : k ≤ b) {p ε δ : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ ≤ 19 / 20) (hfit : generalWideKrylovRank p k ε < b) :
    (generalConvertedAlgorithm.{u} p a b k ε hka hkb).Succeeds p ε δ := by
  intro A
  exact hδ.trans ((refinedPairedKrylovAlgorithm_general_success hk0 hka Aᵀ hp hε hε1 hfit).trans
    (convertedPairedKrylovAlgorithm_success_probability_ge hka hkb (by linarith : 0 < p) A))

theorem rectangularQueryComplexity_le_general_row_log {a b k : ℕ} (hk0 : 0 < k) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal ((k : ℝ) * accuracyScale ε * generalQueryLogFactor p a k ε) := by
  by_cases hfit : generalWideKrylovRank p k ε < a
  · have hka : k ≤ a := (generalWideKrylovRank_ge p k ε).trans hfit.le
    have hbudget := rectangularQueryComplexity_le_budget (generalPairedAlgorithm.{u} p a b k ε hka hkb)
      (generalPairedAlgorithm_succeeds hk0 hka hkb hp hε hε1 hδ hfit)
    have hb := generalPairedQueryBudget_add_rank_le (p := p) (a := a) hk0 hε hε1
    have hkz : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    apply hbudget.trans
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal
      (by linarith : (generalPairedQueryBudget p a k ε : ℝ) ≤
        (k : ℝ) * accuracyScale ε * generalQueryLogFactor p a k ε)
  · have hdim := rectangularQueryComplexity_le_dimension.{u} (a := a) hkb (by linarith : 0 < p)
      hε.le (by linarith : δ ≤ 1)
    have ha : (a : ℝ) ≤ (generalWideKrylovRank p k ε : ℝ) := by exact_mod_cast (le_of_not_gt hfit)
    have hw := generalWideKrylovRank_le (p := p) hk0 hε hε1
    have hf := generalQueryLogFactor_ge (p := p) (a := a) hk0 hε hε1
    have hks : 0 ≤ (k : ℝ) * accuracyScale ε := mul_nonneg (Nat.cast_nonneg k) (accuracyScale_pos hε).le
    have hm : ((min a b : ℕ) : ℝ) ≤ a := by exact_mod_cast (Nat.min_le_left a b)
    have hbound : ((min a b : ℕ) : ℝ) ≤ (k : ℝ) * accuracyScale ε * generalQueryLogFactor p a k ε := by
      calc
        _ ≤ (generalWideKrylovRank p k ε : ℝ) := hm.trans ha
        _ ≤ ((4 : ℝ) ^ (p / 2) + 2) * ((k : ℝ) * accuracyScale ε) := hw
        _ ≤ _ := by nlinarith
    apply hdim.trans
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound

theorem rectangularQueryComplexity_le_general_minimum_log {a b k : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal ((k : ℝ) * accuracyScale ε * generalQueryLogFactor p (min a b) k ε) := by
  by_cases hab : a ≤ b
  · rw [Nat.min_eq_left hab]
    exact rectangularQueryComplexity_le_general_row_log hk0 hkb hp hε hε1 hδ
  · rw [Nat.min_eq_right (le_of_not_ge hab)]
    by_cases hfit : generalWideKrylovRank p k ε < b
    · have hbudget := rectangularQueryComplexity_le_budget (generalConvertedAlgorithm.{u} p a b k ε hka hkb)
        (generalConvertedAlgorithm_succeeds hk0 hka hkb hp hε hε1 hδ hfit)
      have hb := generalPairedQueryBudget_add_rank_le (p := p) (a := b) hk0 hε hε1
      have hbound : (generalConvertedQueryBudget p b k ε : ℝ) ≤
          (k : ℝ) * accuracyScale ε * generalQueryLogFactor p b k ε := by
        rw [generalConvertedQueryBudget_eq, Nat.cast_add]
        simpa only [add_comm] using hb
      apply hbudget.trans
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound
    · have hdim := rectangularQueryComplexity_le_dimension.{u} (a := a) hkb (by linarith : 0 < p)
        hε.le (by linarith : δ ≤ 1)
      rw [Nat.min_eq_right (le_of_not_ge hab)] at hdim
      have hb : (b : ℝ) ≤ (generalWideKrylovRank p k ε : ℝ) := by exact_mod_cast (le_of_not_gt hfit)
      have hw := generalWideKrylovRank_le (p := p) hk0 hε hε1
      have hf := generalQueryLogFactor_ge (p := p) (a := b) hk0 hε hε1
      have hks : 0 ≤ (k : ℝ) * accuracyScale ε := mul_nonneg (Nat.cast_nonneg k) (accuracyScale_pos hε).le
      have hbound : (b : ℝ) ≤ (k : ℝ) * accuracyScale ε * generalQueryLogFactor p b k ε := by
        calc
          _ ≤ ((4 : ℝ) ^ (p / 2) + 2) * ((k : ℝ) * accuracyScale ε) := hb.trans hw
          _ ≤ _ := by nlinarith
      apply hdim.trans
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound

theorem rectangularQueryComplexity_le_general_minimum_rate {a b k : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal (generalQueryLogFactor p (min a b) k ε * targetRate (min a b) k ε) := by
  have hf := generalQueryLogFactor_ge (p := p) (a := min a b) hk0 hε hε1
  have hpow : 0 ≤ (4 : ℝ) ^ (p / 2) := Real.rpow_nonneg (by norm_num) _
  by_cases hmin : ((min a b : ℕ) : ℝ) ≤ (k : ℝ) * accuracyScale ε
  · unfold targetRate
    rw [min_eq_left hmin]
    have hdim := rectangularQueryComplexity_le_dimension.{u} (a := a) hkb (by linarith : 0 < p)
      hε.le (by linarith : δ ≤ 1)
    apply hdim.trans
    have hbound : ((min a b : ℕ) : ℝ) ≤ generalQueryLogFactor p (min a b) k ε * ((min a b : ℕ) : ℝ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith : 1 ≤ generalQueryLogFactor p (min a b) k ε)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound
  · unfold targetRate
    rw [min_eq_right (le_of_not_ge hmin)]
    simpa only [mul_comm] using
      rectangularQueryComplexity_le_general_minimum_log.{u} hk0 hka hkb hp hε hε1 hδ

end
end LowRank
