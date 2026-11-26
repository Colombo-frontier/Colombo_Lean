import SecondOrder.FiniteRelativeEntropy
import SecondOrder.Entropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

def binaryPMF (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.bernoulli (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp1)

@[simp] theorem binaryPMF_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryPMF p hp0 hp1 true = ENNReal.ofReal p := rfl

@[simp] theorem binaryPMF_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryPMF p hp0 hp1 false = ENNReal.ofReal (1-p) := by
  change 1-ENNReal.ofReal p = ENNReal.ofReal (1-p)
  rw [ENNReal.ofReal_sub 1 hp0]
  simp

@[simp] theorem binaryPMF_true_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryPMF p hp0 hp1 true).toReal = p := by simp [hp0]

@[simp] theorem binaryPMF_false_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryPMF p hp0 hp1 false).toReal = 1-p := by simp [sub_nonneg.mpr hp1]

theorem binaryPMF_ne_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    binaryPMF p hp0.le hp1.le b ≠ 0 := by
  cases b
  · rw [binaryPMF_false]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp1)).ne'
  · rw [binaryPMF_true]
    exact (ENNReal.ofReal_pos.mpr hp0).ne'

theorem weighted_log_div (x y : ℝ) (hy : y ≠ 0) :
    x*Real.log (x/y) = x*Real.log x-x*Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hx hy]; ring

theorem pmfKL_binary {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    pmfKL (binaryPMF p hp0 hp1) (binaryPMF q hq0.le hq1.le) = binaryKL p q := by
  simp only [pmfKL, Fintype.sum_bool, binaryPMF_true_toReal, binaryPMF_false_toReal]
  rw [weighted_log_div p q hq0.ne', weighted_log_div (1-p) (1-q) (sub_pos.mpr hq1).ne']
  unfold binaryKL
  ring

/-- The manuscript's binary information lower bound for the actual KL of
Bernoulli measures. Both endpoints of p and the boundary q=1 are included. -/
theorem klDiv_binary_lower {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (p*Real.log (1/q)-Real.log 2) ≤
      klDiv (binaryPMF p hp0 hp1).toMeasure (binaryPMF q hq0.le hq1).toMeasure := by
  rcases hq1.eq_or_lt with hq | hq
  · subst q
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simp only [div_one, Real.log_one, mul_zero, zero_sub,
      ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hl), zero_le]
  · rw [klDiv_pmf _ _ (binaryPMF_ne_zero hq0 hq), pmfKL_binary hp0 hp1 hq0 hq]
    exact ENNReal.ofReal_le_ofReal (binary_entropy_lower hp0 hp1 hq0 hq)

/-- A positive event probability cannot be compared at finite KL cost to
a reference probability of zero. This handles the support boundary. -/
theorem klDiv_binary_zero_reference {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    klDiv (binaryPMF p hp0.le hp1).toMeasure
      (binaryPMF 0 (by norm_num) (by norm_num)).toMeasure = ∞ := by
  apply klDiv_of_not_ac
  intro hac
  have hz : (binaryPMF 0 (by norm_num) (by norm_num)).toMeasure {true} = 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]; simp
  have hp := hac hz
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), binaryPMF_true] at hp
  exact (ENNReal.ofReal_pos.mpr hp0).ne' hp

end
end SecondOrder
