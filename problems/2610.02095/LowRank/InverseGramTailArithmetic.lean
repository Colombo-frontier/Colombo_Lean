import LowRank.GaussianMomentArithmetic
import LowRank.InverseGramMomentTail

/-! Real-valued forms and elementary bounds for the inverse Gram tail coefficient. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

def inverseGramMomentBound (n m : ℕ) (v : NNReal) (a : ℝ) : ℝ :=
  gaussianMomentFormula n a * ((v : ℝ) ^ (-a) * gaussianMomentFormula m (-a)) /
    gaussianMomentFormula 1 a

theorem inverseGram_tail_le_ofReal {d s : ℕ} (hs : s + 1 ≤ d)
    {v : NNReal} (hv : v ≠ 0) (i : Fin (s + 1)) {a R : ℝ} (ha : 0 ≤ a)
    (hd : 0 < ((d - s : ℕ) : ℝ) / 2 - a) (hR : 0 < R) :
    (iidMatrixLaw d (s + 1) v) {X | R < inverseGramEigenvalue X i} ≤
      ENNReal.ofReal (inverseGramMomentBound (s + 1) (d - s) v a / R ^ a) := by
  have hn : 0 ≤ gaussianMomentFormula (s + 1) a :=
    (gaussianMomentFormula_pos (by omega) (by positivity)).le
  have hden : 0 < gaussianMomentFormula 1 a :=
    gaussianMomentFormula_pos (by omega) (by norm_num; linarith)
  have h := inverseGramEigenvalue_tail_le hs hv i ha hd hR
  rw [← ENNReal.ofReal_mul hn, ← ENNReal.ofReal_div_of_pos hden,
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hR a)] at h
  exact h

theorem inverseGramMomentBound_nat_le {n m q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hqm : 2 * q < m) (v : NNReal) :
    inverseGramMomentBound n m v q ≤
      (((n : ℝ) + 2 * q) * (v : ℝ)⁻¹ * Real.exp 1 /
        ((q : ℝ) * ((m : ℝ) - 2 * q))) ^ q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hgap : 0 < (m : ℝ) - 2 * q := by
    have h : 2 * (q : ℝ) < m := by exact_mod_cast hqm
    linarith
  have hneg : 0 ≤ gaussianMomentFormula m (-(q : ℝ)) :=
    (gaussianMomentFormula_pos (by omega) (by linarith)).le
  have hnum := mul_le_mul (gaussianMomentFormula_nat_le hn q)
    (mul_le_mul_of_nonneg_left (gaussianMomentFormula_neg_nat_le hqm)
      (pow_nonneg (inv_nonneg.mpr v.coe_nonneg) q))
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr v.coe_nonneg) q) hneg) (by positivity)
  have hden : 0 < ((q : ℝ) / Real.exp 1) ^ q := by positivity
  unfold inverseGramMomentBound
  rw [Real.rpow_neg v.coe_nonneg, Real.rpow_natCast, ← inv_pow]
  calc
    _ ≤ (((n : ℝ) + 2 * q) ^ q * ((v : ℝ)⁻¹ ^ q * (((m : ℝ) - 2 * q) ^ q)⁻¹)) /
        (((q : ℝ) / Real.exp 1) ^ q) :=
      div_le_div₀ (by positivity) hnum hden (gaussianMomentFormula_one_nat_ge q)
    _ = _ := by
      rw [← inv_pow, ← mul_pow, ← mul_pow, ← div_pow]
      congr 1
      field_simp
      ring

theorem inverseGramMomentBound_half_le {n : ℕ} (hn : 0 < n) (v : NNReal) :
    inverseGramMomentBound n 2 (v : NNReal) (1 / 2) ≤
      4 * Real.sqrt n * Real.sqrt ((v : ℝ)⁻¹) := by
  have hvpow : (v : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt ((v : ℝ)⁻¹) := by
    rw [Real.sqrt_eq_rpow, Real.inv_rpow v.coe_nonneg, Real.rpow_neg v.coe_nonneg]
  have hnum : gaussianMomentFormula n (1 / 2) *
      ((v : ℝ) ^ (-(1 / 2 : ℝ)) * gaussianMomentFormula 2 (-(1 / 2))) ≤
        Real.sqrt n * (Real.sqrt ((v : ℝ)⁻¹) * 2) := by
    rw [hvpow]
    apply mul_le_mul (gaussianMomentFormula_half_le_sqrt hn)
      (mul_le_mul_of_nonneg_left gaussianMomentFormula_two_neg_half_le (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (gaussianMomentFormula_pos (by omega) (by norm_num)).le)
      (Real.sqrt_nonneg _)
  unfold inverseGramMomentBound
  have h := div_le_div₀ (by positivity) hnum (by norm_num : (0 : ℝ) < 1 / 2)
    gaussianMomentFormula_one_half_ge
  convert h using 1 <;> ring

end
end LowRank
