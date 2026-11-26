import LowRank.CubicPairedKrylovBudget
import LowRank.ExactRecoveryUpperBound

/-! For 1 <= p <= 2 the true minimax query complexity has the cubic-root
upper rate, with an explicit logarithmic multiplier. Exact recovery covers
dimensions too small for the wide block and also supplies the dimension cap. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

def cubicPairedAlgorithm (a b k : ℕ) (ε : ℝ) (hka : k ≤ a) (hkb : k ≤ b) :
    RectangularColumnAlgorithm.{u} a b k (cubicPairedQueryBudget a k ε) :=
  refinedPairedKrylovAlgorithm a b k (2 * k + 2) (2 * wideKrylovRank k ε + 2)
    (chebyshevFilterDegree (cubicKrylovGap ε) (cubicNarrowTolerance a k ε) + 1)
    (chebyshevFilterDegree 1 (cubicWideTolerance a k ε) + 1) hka hkb

theorem cubicPairedAlgorithm_succeeds {a b k : ℕ} (hk0 : 0 < k)
    (hka : k ≤ a) (hkb : k ≤ b) {p ε δ : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ ≤ 19 / 20) (hfit : wideKrylovRank k ε < a) :
    (cubicPairedAlgorithm.{u} a b k ε hka hkb).Succeeds p ε δ := by
  intro A
  exact hδ.trans (refinedPairedKrylovAlgorithm_cubic_success hk0 hkb A hp hp2 hε hε1 hfit)

theorem rectangularQueryComplexity_le_cubic_log {a b k : ℕ} (hk0 : 0 < k) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal ((k : ℝ) * accuracyScale ε * cubicQueryLogFactor a k ε) := by
  by_cases hfit : wideKrylovRank k ε < a
  · have hka : k ≤ a := (wideKrylovRank_ge k ε).trans hfit.le
    have hbudget := rectangularQueryComplexity_le_budget (cubicPairedAlgorithm.{u} a b k ε hka hkb)
      (cubicPairedAlgorithm_succeeds hk0 hka hkb hp hp2 hε hε1 hδ hfit)
    apply hbudget.trans
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal
      (cubicPairedQueryBudget_le (a := a) hk0 hε hε1)
  · have hdim := rectangularQueryComplexity_le_dimension.{u} (a := a) hkb (by linarith : 0 < p)
      hε.le (by linarith : δ ≤ 1)
    have ha : (a : ℝ) ≤ (wideKrylovRank k ε : ℝ) := by exact_mod_cast (le_of_not_gt hfit)
    have hw := wideKrylovRank_le hk0 hε hε1
    have hf := cubicQueryLogFactor_ge (a := a) hk0 hε hε1
    have hks : 0 ≤ (k : ℝ) * accuracyScale ε := mul_nonneg (Nat.cast_nonneg k) (accuracyScale_pos hε).le
    have hm : ((min a b : ℕ) : ℝ) ≤ a := by exact_mod_cast (Nat.min_le_left a b)
    have hbound : ((min a b : ℕ) : ℝ) ≤ (k : ℝ) * accuracyScale ε * cubicQueryLogFactor a k ε := by
      calc
        _ ≤ (wideKrylovRank k ε : ℝ) := hm.trans ha
        _ ≤ 6 * ((k : ℝ) * accuracyScale ε) := hw
        _ ≤ _ := by nlinarith
    apply hdim.trans
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound

theorem rectangularQueryComplexity_le_cubic_min {a b k : ℕ} (hk0 : 0 < k) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      min (((min a b : ℕ) : ℝ≥0∞))
        (ENNReal.ofReal ((k : ℝ) * accuracyScale ε * cubicQueryLogFactor a k ε)) :=
  le_min (rectangularQueryComplexity_le_dimension hkb (by linarith : 0 < p) hε.le (by linarith : δ ≤ 1))
    (rectangularQueryComplexity_le_cubic_log hk0 hkb hp hp2 hε hε1 hδ)

theorem rectangularQueryComplexity_le_cubic_rate {a b k : ℕ} (hk0 : 0 < k) (hkb : k ≤ b)
    {p ε δ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 19 / 20) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤
      ENNReal.ofReal (cubicQueryLogFactor a k ε * targetRate (min a b) k ε) := by
  have hf := cubicQueryLogFactor_ge (a := a) hk0 hε hε1
  by_cases hmin : ((min a b : ℕ) : ℝ) ≤ (k : ℝ) * accuracyScale ε
  · unfold targetRate
    rw [min_eq_left hmin]
    have hdim := rectangularQueryComplexity_le_dimension.{u} (a := a) hkb (by linarith : 0 < p)
      hε.le (by linarith : δ ≤ 1)
    apply hdim.trans
    have hbound : ((min a b : ℕ) : ℝ) ≤ cubicQueryLogFactor a k ε * ((min a b : ℕ) : ℝ) :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith : 1 ≤ cubicQueryLogFactor a k ε)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hbound
  · unfold targetRate
    rw [min_eq_right (le_of_not_ge hmin)]
    simpa only [mul_comm] using rectangularQueryComplexity_le_cubic_log.{u} hk0 hkb hp hp2 hε hε1 hδ

end
end LowRank
