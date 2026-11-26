import LowRank.InverseGramTailArithmetic

/-! Dimension-uniform constants for the three inverse Gram moment regimes. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

def wishartInverseThreshold (d k : ℕ) : ℝ := 1000000 * (d : ℝ) ^ 2 / (k : ℝ) ^ 2

theorem wishartInverseThreshold_pos {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    0 < wishartInverseThreshold d k := by unfold wishartInverseThreshold; positivity

theorem inverseGramMomentBound_large {d n k : ℕ} (hn : 0 < n)
    (hsize : n + k = d) (hk : 4 ≤ k) :
    inverseGramMomentBound n (k + 1) (d : NNReal)⁻¹ (k / 4 : ℕ) ≤
      (48 * (d : ℝ) ^ 2 / (k : ℝ) ^ 2) ^ (k / 4) := by
  let q := k / 4
  have hq : 0 < q := by dsimp [q]; omega
  have h8 : k ≤ 8 * q := by dsimp [q]; omega
  have h4 : 4 * q ≤ k := by dsimp [q]; omega
  have hqm : 2 * q < k + 1 := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsizeR : (n : ℝ) + k = d := by exact_mod_cast hsize
  have h4R : 4 * (q : ℝ) ≤ k := by exact_mod_cast h4
  have h8R : (k : ℝ) ≤ 8 * q := by exact_mod_cast h8
  have hgap : 0 < (k : ℝ) + 1 - 2 * q := by linarith
  have hnq : (n : ℝ) + 2 * q ≤ d := by linarith
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hnum : ((n : ℝ) + 2 * q) * d * Real.exp 1 ≤ 3 * (d : ℝ) ^ 2 := by
    calc
      _ ≤ (d : ℝ) * d * 3 := mul_le_mul
        (mul_le_mul_of_nonneg_right hnq hdR.le) hexp (Real.exp_pos 1).le (by positivity)
      _ = _ := by ring
  have hden : (k : ℝ) ^ 2 / 16 ≤ (q : ℝ) * ((k : ℝ) + 1 - 2 * q) := by
    have h := mul_le_mul (show (k : ℝ) / 8 ≤ q by linarith)
      (show (k : ℝ) / 2 ≤ (k : ℝ) + 1 - 2 * q by linarith) (by positivity) hqR.le
    nlinarith
  have hbase : (((n : ℝ) + 2 * q) * d * Real.exp 1 /
      ((q : ℝ) * ((k : ℝ) + 1 - 2 * q))) ≤ 48 * (d : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
    calc
      _ ≤ (3 * (d : ℝ) ^ 2) / ((k : ℝ) ^ 2 / 16) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by field_simp; ring
  have h := inverseGramMomentBound_nat_le hn hq hqm (d : NNReal)⁻¹
  simp only [NNReal.coe_inv, NNReal.coe_natCast, inv_inv, Nat.cast_add, Nat.cast_one] at h
  exact h.trans (pow_le_pow_left₀ (by positivity) hbase q)

theorem inverseGramMomentBound_large_ratio {d n k : ℕ} (hn : 0 < n)
    (hsize : n + k = d) (hk : 4 ≤ k) :
    inverseGramMomentBound n (k + 1) (d : NNReal)⁻¹ (k / 4 : ℕ) /
      wishartInverseThreshold d k ^ (k / 4) ≤ 1 / 40 := by
  have hd : 0 < d := by omega
  have hk0 : 0 < k := by omega
  have hq : k / 4 ≠ 0 := by omega
  have hR := wishartInverseThreshold_pos hd hk0
  calc
    _ ≤ (48 * (d : ℝ) ^ 2 / (k : ℝ) ^ 2) ^ (k / 4) /
        wishartInverseThreshold d k ^ (k / 4) :=
      div_le_div_of_nonneg_right (inverseGramMomentBound_large hn hsize hk)
        (pow_nonneg hR.le _)
    _ = (48 / 1000000 : ℝ) ^ (k / 4) := by
      rw [← div_pow]
      congr 1
      unfold wishartInverseThreshold
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
      field_simp
      ring
    _ ≤ 48 / 1000000 := pow_le_of_le_one (by norm_num) (by norm_num) hq
    _ ≤ 1 / 40 := by norm_num

theorem inverseGramMomentBound_first {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (v : NNReal) :
    inverseGramMomentBound n (k + 1) v 1 = (n : ℝ) * (v : ℝ)⁻¹ / ((k : ℝ) - 1) := by
  unfold inverseGramMomentBound
  rw [gaussianMomentFormula_one hn, gaussianMomentFormula_one (by omega : 0 < 1)]
  have hneg := gaussianMomentFormula_neg_nat (m := k + 1) (q := 1) (by omega)
  norm_num at hneg
  rw [hneg, Real.rpow_neg_one]
  norm_num
  ring

theorem inverseGramMomentBound_small_ratio {d n k : ℕ} (hn : 0 < n)
    (hsize : n + k = d) (hk : 2 ≤ k) (hk3 : k ≤ 3) :
    inverseGramMomentBound n (k + 1) (d : NNReal)⁻¹ 1 /
      wishartInverseThreshold d k ≤ 1 / 40 := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnd : (n : ℝ) ≤ d := by exact_mod_cast (show n ≤ d by omega)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 1 := by linarith
  have hbound : inverseGramMomentBound n (k + 1) (d : NNReal)⁻¹ 1 ≤ (d : ℝ) ^ 2 := by
    rw [inverseGramMomentBound_first hn hk, NNReal.coe_inv, NNReal.coe_natCast, inv_inv]
    calc
      _ ≤ (n : ℝ) * d := div_le_self (by positivity) (by linarith)
      _ ≤ (d : ℝ) ^ 2 := by nlinarith
  have hR := wishartInverseThreshold_pos hd (by omega : 0 < k)
  calc
    _ ≤ (d : ℝ) ^ 2 / wishartInverseThreshold d k :=
      div_le_div_of_nonneg_right hbound hR.le
    _ = (k : ℝ) ^ 2 / 1000000 := by
      unfold wishartInverseThreshold
      field_simp
      ring
    _ ≤ 1 / 40 := by
      have hk3R : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
      nlinarith

theorem inverseGramMomentBound_half_normalized {d n : ℕ} (hn : 0 < n) (hnd : n ≤ d) :
    inverseGramMomentBound n 2 (d : NNReal)⁻¹ (1 / 2) ≤ 4 * d := by
  have h := inverseGramMomentBound_half_le hn (d : NNReal)⁻¹
  simp only [NNReal.coe_inv, NNReal.coe_natCast, inv_inv] at h
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnd)
  calc
    _ ≤ 4 * Real.sqrt (n : ℝ) * Real.sqrt (d : ℝ) := h
    _ ≤ 4 * Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) := by gcongr
    _ = 4 * d := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg d)]

theorem inverseGramMomentBound_half_ratio {d n : ℕ} (hn : 0 < n) (hnd : n ≤ d) :
    inverseGramMomentBound n 2 (d : NNReal)⁻¹ (1 / 2) /
      wishartInverseThreshold d 1 ^ (1 / 2 : ℝ) ≤ 1 / 40 := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : wishartInverseThreshold d 1 ^ (1 / 2 : ℝ) = 1000 * (d : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity : (0 : ℝ) < 1000 * d)).2
    simp only [wishartInverseThreshold, Nat.cast_one, one_pow, div_one]
    ring
  rw [he]
  calc
    _ ≤ (4 * (d : ℝ)) / (1000 * d) := div_le_div_of_nonneg_right
      (inverseGramMomentBound_half_normalized hn hnd) (by positivity)
    _ = 4 / 1000 := by field_simp; ring
    _ ≤ 1 / 40 := by norm_num

end
end LowRank
