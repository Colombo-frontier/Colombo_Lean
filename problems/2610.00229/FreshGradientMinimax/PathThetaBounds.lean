import FreshGradientMinimax.PathParameters
import Mathlib.Data.Complex.ExponentialBounds

/-! Quantitative hyperbolic bounds for the calibrated path. The intermediate
constants are deliberately coarse; they retain the paper's final 1/1024
localization constant and require no assumptions about a hard instance. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax

theorem cosh_quadratic_lower {t : ℝ} (ht : 0 ≤ t) : t ^ 2 ≤ 2 * (Real.cosh t - 1) := by
  have hh : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr (by positivity)
  have hs := pow_le_pow_left₀ (show 0 ≤ t / 2 by positivity) hh 2
  have hc := Real.cosh_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hc
  have hi := Real.cosh_sq_sub_sinh_sq (t / 2)
  nlinarith only [hs, hc, hi]

theorem pathTheta_condition_identity (p : Parameters) :
    p.κ * (Real.cosh (pathTheta p.μ (p.L / 8192)) - 1) = 4096 := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  rw [pathTheta_cosh p.μ_pos (by positivity)]
  unfold Parameters.κ
  field_simp [hL.ne', p.μ_pos.ne']
  ring

theorem pathTheta_sq_condition (p : Parameters) :
    pathTheta p.μ (p.L / 8192) ^ 2 * p.κ ≤ 8192 := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hθ := pathTheta_pos p.μ_pos (by positivity : 0 < p.L / 8192)
  have hκ : 0 ≤ p.κ := (by norm_num : (0 : ℝ) ≤ 1).trans p.condition_ge_one
  have hm := mul_le_mul_of_nonneg_right (cosh_quadratic_lower hθ.le) hκ
  have he := pathTheta_condition_identity p
  nlinarith only [hm, he]

theorem pathTheta_sinh_sq_condition (p : Parameters) :
    8192 ≤ Real.sinh (pathTheta p.μ (p.L / 8192)) ^ 2 * p.κ := by
  have hκ : 0 ≤ p.κ := (by norm_num : (0 : ℝ) ≤ 1).trans p.condition_ge_one
  have hs : 2 * (Real.cosh (pathTheta p.μ (p.L / 8192)) - 1) ≤
      Real.sinh (pathTheta p.μ (p.L / 8192)) ^ 2 := by
    rw [Real.sinh_sq]
    nlinarith [sq_nonneg (Real.cosh (pathTheta p.μ (p.L / 8192)) - 1)]
  have hm := mul_le_mul_of_nonneg_right hs hκ
  have he := pathTheta_condition_identity p
  nlinarith only [hm, he]

theorem pathTheta_condition_bounds (p : Parameters) (hκ : 8192 ≤ p.κ) :
    pathTheta p.μ (p.L / 8192) ≤ 1 ∧
      pathTheta p.μ (p.L / 8192) * Real.sqrt p.κ ≤ 128 ∧
      1 ≤ Real.sinh (pathTheta p.μ (p.L / 8192)) * Real.sqrt p.κ := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hθ := pathTheta_pos p.μ_pos (by positivity : 0 < p.L / 8192)
  have hk : 0 < p.κ := by linarith
  have hr : 0 ≤ Real.sqrt p.κ := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt p.κ) ^ 2 = p.κ := Real.sq_sqrt hk.le
  have hθ2 := pathTheta_sq_condition p
  have hs2 := pathTheta_sinh_sq_condition p
  have hs : 0 ≤ Real.sinh (pathTheta p.μ (p.L / 8192)) := Real.sinh_nonneg_iff.mpr hθ.le
  have hθone : pathTheta p.μ (p.L / 8192) ^ 2 ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right hk).mp
    nlinarith only [hθ2, hκ]
  refine ⟨by nlinarith only [hθone], ?_, ?_⟩
  · apply (sq_le_sq₀ (mul_nonneg hθ.le hr) (by norm_num : (0 : ℝ) ≤ 128)).mp
    rw [mul_pow, hr2]
    nlinarith only [hθ2]
  · apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hs hr)).mp
    rw [mul_pow, hr2]
    nlinarith only [hs2]

theorem exp_five_le : Real.exp 5 ≤ 243 := by
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 5
  have hid : Real.exp 5 = Real.exp 1 ^ 5 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 5
  rw [hid]
  norm_num at hp ⊢
  exact hp

end FreshGradientMinimax
