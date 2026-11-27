import Mathlib

namespace Task006.UpperLogBudget

lemma square_le_exp_quarter (s : ℝ) (hs : 0 ≤ s) : s^2 ≤ 32 * Real.exp (s/4) := by
  have h := Real.pow_div_factorial_le_exp (s/4) (by linarith : 0 ≤ s/4) 2
  norm_num at h
  nlinarith

theorem log_budget (K d A : ℝ) (hK : 1 ≤ K) (hd : 2 ≤ d) (hA : 2 ≤ A) (_hdA : d ≤ A) :
    let Cs := 16 + 4 * Real.log (32*K+1)
    let s := Cs * Real.log (Real.exp 1 * d * A)
    let T := Nat.ceil (K*A^3*s^(3/2:ℝ))
    1 ≤ s ∧ 1 ≤ T ∧ (T:ℝ)*d*Real.exp (-s) ≤ A⁻¹^2 := by
  let C := 32*K+1
  let u := Real.log (Real.exp 1*d*A)
  let s := (16+4*Real.log C)*u
  let z := K*A^3*s^(3/2:ℝ)
  change 1 ≤ s ∧ 1 ≤ Nat.ceil z ∧ (Nat.ceil z:ℝ)*d*Real.exp (-s) ≤ A⁻¹^2
  have hK0 : 0 < K := by linarith
  have hd0 : 0 < d := by linarith
  have hA0 : 0 < A := by linarith
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 < C := by linarith
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hld : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hlA : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hu : u = 1+Real.log d+Real.log A := by
    dsimp [u]
    rw [Real.log_mul (mul_pos (Real.exp_pos 1) hd0).ne' hA0.ne',
      Real.log_mul (Real.exp_pos 1).ne' hd0.ne',Real.log_exp]
  have hu1 : 1 ≤ u := by linarith
  have hs1 : 1 ≤ s := by dsimp [s]; nlinarith
  have hs0 : 0 ≤ s := by linarith
  have hz0 : 0 < z := by dsimp [z]; positivity
  refine ⟨hs1,by exact Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr hz0),?_⟩
  have hrpow : s^(3/2:ℝ) ≤ s^2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num : (3/2:ℝ) ≤ 2)
    simpa only [Real.rpow_two] using h
  have hAs : 1 ≤ A^3*s^2 := by
    have hAc : 1 ≤ A^3 := one_le_pow₀ (by linarith : 1 ≤ A)
    have hss : 1 ≤ s^2 := one_le_pow₀ hs1
    exact one_le_mul_of_one_le_of_one_le hAc hss
  have hceil : (Nat.ceil z : ℝ) ≤ (K+1)*A^3*s^2 := by
    have hc := Nat.ceil_lt_add_one hz0.le
    have hz : z ≤ K*A^3*s^2 := mul_le_mul_of_nonneg_left hrpow (by positivity)
    nlinarith
  have hlogcoef : Real.log (32*(K+1)) ≤ 2*Real.log C := by
    have hbase : 32*(K+1) ≤ C^2 := by dsimp [C]; nlinarith
    have h := Real.log_le_log (by positivity : 0 < 32*(K+1)) hbase
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have hlogs : Real.log (32*(K+1)) + Real.log d + 5*Real.log A ≤ 3*s/4 := by
    have hmul : 4*Real.log C ≤ 4*Real.log C*u :=
      le_mul_of_one_le_right (by positivity) hu1
    dsimp [s]
    nlinarith
  have hexp : (32*(K+1))*d*A^5*Real.exp (-3*s/4) ≤ 1 := by
    have harg : Real.log (32*(K+1)*d*A^5) - 3*s/4 ≤ 0 := by
      rw [Real.log_mul (mul_pos (by positivity) hd0).ne' (pow_pos hA0 5).ne',
        Real.log_mul (by positivity) hd0.ne',Real.log_pow]
      norm_num
      linarith
    have he := Real.exp_le_exp.mpr harg
    rw [Real.exp_zero,Real.exp_sub,Real.exp_log (by positivity)] at he
    rw [show -3*s/4 = -(3*s/4) by ring,Real.exp_neg]
    convert he using 1 <;> ring
  have hfirst : (Nat.ceil z:ℝ)*d*Real.exp (-s) ≤
      32*(K+1)*d*A^3*Real.exp (-3*s/4) := by
    calc
      _ ≤ ((K+1)*A^3*s^2)*d*Real.exp (-s) := by gcongr
      _ ≤ ((K+1)*A^3*(32*Real.exp (s/4)))*d*Real.exp (-s) := by
        gcongr
        exact square_le_exp_quarter s hs0
      _ = _ := by
        rw [show -3*s/4 = s/4 + -s by ring,Real.exp_add]
        ring
  apply (mul_le_mul_iff_of_pos_right (pow_pos hA0 2)).mp
  have hcancel : A⁻¹^2*A^2 = 1 := by field_simp
  rw [hcancel]
  calc
    _ ≤ (32*(K+1)*d*A^3*Real.exp (-3*s/4))*A^2 :=
      mul_le_mul_of_nonneg_right hfirst (sq_nonneg A)
    _ = (32*(K+1))*d*A^5*Real.exp (-3*s/4) := by ring
    _ ≤ 1 := hexp

end Task006.UpperLogBudget
