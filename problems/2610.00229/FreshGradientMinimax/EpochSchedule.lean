import FreshGradientMinimax.RefreshParameters

/-! Explicit halving envelopes: logarithmically many epochs, but a bounded
sum of inverse envelopes independent of the initial energy. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def finalEpochIndex (E₀ e : ℝ) : ℕ := ⌈Real.log (max E₀ e / e) / Real.log 2⌉₊

def valueEnvelope (E₀ e : ℝ) (j : ℕ) : ℝ := max e (max E₀ e / 2 ^ j)

theorem valueEnvelope_ge (E₀ e : ℝ) (j : ℕ) : e ≤ valueEnvelope E₀ e j := le_max_left _ _

theorem valueEnvelope_initial (E₀ e : ℝ) : E₀ ≤ valueEnvelope E₀ e 0 := by
  simpa only [valueEnvelope, pow_zero, div_one, max_eq_right (le_max_right E₀ e)] using le_max_left E₀ e

theorem valueEnvelope_half {E₀ e : ℝ} (he : 0 < e) (j : ℕ) :
    valueEnvelope E₀ e j / 2 ≤ valueEnvelope E₀ e (j + 1) := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply max_le
  · have h := valueEnvelope_ge E₀ e (j + 1)
    linarith
  · have h := le_max_right e (max E₀ e / 2 ^ (j + 1))
    change _ ≤ valueEnvelope E₀ e (j + 1) at h
    have heq : max E₀ e / 2 ^ j = (max E₀ e / 2 ^ (j + 1)) * 2 := by
      rw [pow_succ]
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right h (by norm_num)

theorem finalEpochIndex_power {E₀ e : ℝ} (he : 0 < e) :
    max E₀ e / e ≤ (2 : ℝ) ^ finalEpochIndex E₀ e ∧
      (2 : ℝ) ^ finalEpochIndex E₀ e < 2 * (max E₀ e / e) := by
  have hR : 1 ≤ max E₀ e / e := (le_div_iff₀ he).mpr (by rw [one_mul]; exact le_max_right E₀ e)
  have hRp : 0 < max E₀ e / e := lt_of_lt_of_le zero_lt_one hR
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_nonneg hR
  have hlo := Nat.le_ceil (Real.log (max E₀ e / e) / Real.log 2)
  have hhi := Nat.ceil_lt_add_one (div_nonneg hlog hl.le)
  change Real.log (max E₀ e / e) / Real.log 2 ≤ (finalEpochIndex E₀ e : ℝ) at hlo
  change (finalEpochIndex E₀ e : ℝ) < Real.log (max E₀ e / e) / Real.log 2 + 1 at hhi
  have hp : (0 : ℝ) < 2 ^ finalEpochIndex E₀ e := by positivity
  constructor
  · apply (Real.log_le_log_iff hRp hp).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hl).mp hlo
  · apply (Real.log_lt_log_iff hp (mul_pos (by norm_num) hRp)).mp
    rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRp.ne']
    have hd : Real.log (max E₀ e / e) / Real.log 2 * Real.log 2 = Real.log (max E₀ e / e) :=
      div_mul_cancel₀ _ hl.ne'
    have hh := mul_lt_mul_of_pos_right hhi hl
    nlinarith only [hh, hd]

theorem valueEnvelope_final {E₀ e : ℝ} (he : 0 < e) :
    valueEnvelope E₀ e (finalEpochIndex E₀ e) = e := by
  apply max_eq_left
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ finalEpochIndex E₀ e)).mpr
  have h := (div_le_iff₀ he).mp (finalEpochIndex_power (E₀ := E₀) he).1
  linarith

theorem finalEpochIndex_count {E₀ e : ℝ} (he : 0 < e) :
    (finalEpochIndex E₀ e + 1 : ℕ) ≤ Real.log (max E₀ e / e) / Real.log 2 + 2 := by
  have hR : 1 ≤ max E₀ e / e := (le_div_iff₀ he).mpr (by rw [one_mul]; exact le_max_right E₀ e)
  have h := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hR)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  change (finalEpochIndex E₀ e : ℝ) < _ at h
  push_cast
  linarith

theorem valueEnvelope_inverse_sum {E₀ e : ℝ} (he : 0 < e) :
    (∑ j ∈ Finset.range (finalEpochIndex E₀ e + 1), 1 / valueEnvelope E₀ e j) ≤ 4 / e := by
  have hM : 0 < max E₀ e := he.trans_le (le_max_right _ _)
  have hterm (j : ℕ) : 1 / valueEnvelope E₀ e j ≤ 2 ^ j / max E₀ e := by
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hh := one_div_le_one_div_of_le (div_pos hM hp) (le_max_right e (max E₀ e / 2 ^ j))
    simpa only [one_div_div] using hh
  calc
    _ ≤ ∑ j ∈ Finset.range (finalEpochIndex E₀ e + 1), 2 ^ j / max E₀ e :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = ((2 : ℝ) ^ (finalEpochIndex E₀ e + 1) - 1) / max E₀ e := by
      rw [← Finset.sum_div, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      norm_num
    _ ≤ 4 / e := by
      apply (div_le_div_iff₀ hM he).mpr
      have h := (finalEpochIndex_power (E₀ := E₀) he).2
      have hh := mul_lt_mul_of_pos_right h he
      have hd : (max E₀ e / e) * e = max E₀ e := div_mul_cancel₀ _ he.ne'
      rw [pow_succ]
      nlinarith only [hh, hd, he]

end FreshGradientMinimax
