import HeavyTail.Envelope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-! Exact scalar calibration for the manuscript's simultaneous independent
Bernoulli coordinate oracle. This module assumes no probability bounds. -/

noncomputable section
namespace HeavyTail.IndependentBernoulli

def sourceAmplitude (G L p : ℝ) (k : ℕ) (α : ℝ) : ℝ :=
  (1 / 16) * min G (L * (k : ℝ) ^ (1 / 2 - 1 / p) * α ^ (1 - 1 / p))

theorem sourceAmplitude_nonneg {G L p α : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hα : 0 ≤ α) (k : ℕ) : 0 ≤ sourceAmplitude G L p k α := by
  unfold sourceAmplitude
  positivity

theorem sourceAmplitude_pos {G L p α : ℝ} (hG : 0 < G) (hL : 0 < L)
    (hα : 0 < α) {k : ℕ} (hk : 0 < k) : 0 < sourceAmplitude G L p k α := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  unfold sourceAmplitude
  positivity

theorem sourceAmplitude_le_G {G L p α : ℝ} (hG : 0 ≤ G) (k : ℕ) :
    sourceAmplitude G L p k α ≤ G := by
  unfold sourceAmplitude
  calc
    _ ≤ (1 / 16 : ℝ) * G := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    _ ≤ G := by linarith

theorem unscaled_power_identity {L p K α d : ℝ} (hL : 0 ≤ L)
    (hp : 0 < p) (hK : 0 < K) (hα : 0 < α) :
    (L * K ^ (1 / 2 - 1 / p) * α ^ (1 - 1 / p)) ^ p * K ^ d * α ^ (1 - p) =
      L ^ p * K ^ (p / 2 - 1 + d) := by
  have heK : (1 / 2 - 1 / p) * p = p / 2 - 1 := by field_simp [hp.ne']; ring
  have heα : (1 - 1 / p) * p + (1 - p) = 0 := by field_simp [hp.ne']
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hL (by positivity),
    ← Real.rpow_mul hK.le, ← Real.rpow_mul hα.le]
  calc
    _ = L ^ p * (K ^ ((1 / 2 - 1 / p) * p) * K ^ d) *
        (α ^ ((1 - 1 / p) * p) * α ^ (1 - p)) := by ring
    _ = _ := by rw [← Real.rpow_add hK, ← Real.rpow_add hα, heK, heα, Real.rpow_zero, mul_one]

theorem sourceAmplitude_power_budget {k : ℕ} (hk : 0 < k) {G L p α : ℝ}
    (hG : 0 ≤ G) (hL : 0 ≤ L) (hp : 1 ≤ p) (hα : 0 < α) :
    16 * (sourceAmplitude G L p k α) ^ p ≤
      (L * (k : ℝ) ^ (1 / 2 - 1 / p) * α ^ (1 - 1 / p)) ^ p := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ha := sourceAmplitude_nonneg (p := p) hG hL hα.le k
  have hbound : sourceAmplitude G L p k α ≤
      (L * (k : ℝ) ^ (1 / 2 - 1 / p) * α ^ (1 - 1 / p)) / 16 := by
    unfold sourceAmplitude
    have hh := mul_le_mul_of_nonneg_left
      (min_le_right G (L * (k : ℝ) ^ (1 / 2 - 1 / p) * α ^ (1 - 1 / p)))
      (by norm_num : (0 : ℝ) ≤ 1 / 16)
    convert hh using 1 <;> ring
  have hpow := Real.rpow_le_rpow ha hbound (zero_le_one.trans hp)
  rw [Real.div_rpow (by positivity) (by norm_num)] at hpow
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 16) p)).mp hpow
  have h16 : (16 : ℝ) ≤ (16 : ℝ) ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 16) hp
  have hmul := mul_le_mul_of_nonneg_left h16 (Real.rpow_nonneg ha p)
  nlinarith only [hh, hmul]

theorem sourceAmplitude_two_moment_budgets {k : ℕ} (hk : 0 < k) {G L s p α : ℝ}
    (hG : 0 ≤ G) (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hα : 0 < α) (hdim : L ^ 2 ≤ (k : ℝ) * s ^ 2) :
    2 * (sourceAmplitude G L p k α) ^ p * (k : ℝ) ^ (1 - p / 2) * α ^ (1 - p) ≤ L ^ p ∧
    (2 : ℝ) ^ (p + 1) * (sourceAmplitude G L p k α) ^ p *
      (k : ℝ) ^ (1 - p) * α ^ (1 - p) ≤ s ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ha := sourceAmplitude_nonneg (p := p) hG hL hα.le k
  have hpow := Real.rpow_nonneg ha p
  have hbudget := sourceAmplitude_power_budget hk hG hL hp hα
  have hstrong : 2 * (sourceAmplitude G L p k α) ^ p ≤
      (L * (k : ℝ) ^ (1 / 2 - 1 / p) * α ^ (1 - 1 / p)) ^ p := by
    linarith only [hpow, hbudget]
  have h2 : (2 : ℝ) ^ (p + 1) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show p + 1 ≤ 3 by linarith)
    have hr : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
      norm_num
    simpa only [hr] using hh
  have hweak : (2 : ℝ) ^ (p + 1) * (sourceAmplitude G L p k α) ^ p ≤
      (L * (k : ℝ) ^ (1 / 2 - 1 / p) * α ^ (1 - 1 / p)) ^ p := by
    have hh := mul_le_mul_of_nonneg_right h2 hpow
    linarith only [hh, hpow, hbudget]
  constructor
  · have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hstrong (Real.rpow_nonneg hkR.le (1 - p / 2)))
      (Real.rpow_nonneg hα.le (1 - p))
    rw [unscaled_power_identity hL hp0 hkR hα] at hh
    convert hh using 1 <;> simp only [show p / 2 - 1 + (1 - p / 2) = 0 by ring,
      Real.rpow_zero, mul_one]
  · have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hweak (Real.rpow_nonneg hkR.le (1 - p)))
      (Real.rpow_nonneg hα.le (1 - p))
    rw [unscaled_power_identity hL hp0 hkR hα] at hh
    have hnormal : L ^ p * (k : ℝ) ^ (p / 2 - 1 + (1 - p)) = (L / Real.sqrt k) ^ p := by
      rw [Real.div_rpow hL (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hkR.le]
      rw [show p / 2 - 1 + (1 - p) = -(1 / 2 * p) by ring, Real.rpow_neg hkR.le]
      rfl
    rw [hnormal] at hh
    have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
    have hLs : L / Real.sqrt (k : ℝ) ≤ s := by
      have hsq : (L / Real.sqrt (k : ℝ)) ^ 2 ≤ s ^ 2 := by
        rw [div_pow, Real.sq_sqrt hkR.le]
        exact (div_le_iff₀ hkR).mpr (by simpa only [mul_comm] using hdim)
      nlinarith [div_nonneg hL hsqrt.le]
    exact hh.trans (Real.rpow_le_rpow (div_nonneg hL hsqrt.le) hLs hp0.le)

end HeavyTail.IndependentBernoulli
