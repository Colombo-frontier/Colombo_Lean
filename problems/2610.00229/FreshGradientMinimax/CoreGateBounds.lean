import FreshGradientMinimax.CoreGateSmooth
import FreshGradientMinimax.GaussianPowerBounds

/-! The original uniform constants for sqrt Ψ and the first two derivatives
of Ψ. Every assertion includes the junction and the entire flat half-line. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem coreGateRoot_bound (t : ℝ) : |coreGateRoot t| ≤ 2 := by
  rw [abs_of_nonneg (coreGateRoot_nonneg t)]
  nlinarith [coreGateRoot_sq t, coreGate_le_three t]

theorem coreGateRootDeriv_flat {t : ℝ} (ht : t ≤ 1 / 2) : coreGateRootDeriv t = 0 := by
  simp only [coreGateRootDeriv, coreGateRoot_zero ht, mul_zero]

theorem coreGateRootSecond_flat {t : ℝ} (ht : t ≤ 1 / 2) : coreGateRootSecond t = 0 := by
  simp only [coreGateRootSecond, coreGateRoot_zero ht, mul_zero]

theorem coreGateRootDeriv_nonneg (t : ℝ) : 0 ≤ coreGateRootDeriv t := by
  by_cases ht : t ≤ 1 / 2
  · rw [coreGateRootDeriv_flat ht]
  · unfold coreGateRootDeriv
    have hv : 0 ≤ (2 * t - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hv _)) (coreGateRoot_nonneg t)

theorem coreGateRootDeriv_bound (t : ℝ) : |coreGateRootDeriv t| ≤ 4 := by
  by_cases ht : t ≤ 1 / 2
  · rw [coreGateRootDeriv_flat ht]
    norm_num
  · rw [coreGateRootDeriv, coreGateRoot_active (lt_of_not_ge ht)]
    convert gaussian_cube_derivative_bound ((2 * t - 1)⁻¹) using 1
    congr 1
    ring

theorem coreGateRootSecond_bound (t : ℝ) : |coreGateRootSecond t| ≤ 120 := by
  by_cases ht : t ≤ 1 / 2
  · rw [coreGateRootSecond_flat ht]
    norm_num
  · rw [coreGateRootSecond, coreGateRoot_active (lt_of_not_ge ht)]
    convert gaussian_root_second_bound ((2 * t - 1)⁻¹) using 1
    congr 1
    ring

def coreGateDeriv (t : ℝ) : ℝ := 2 * coreGateRoot t * coreGateRootDeriv t
def coreGateSecond (t : ℝ) : ℝ :=
  2 * coreGateRootDeriv t ^ 2 + 2 * coreGateRoot t * coreGateRootSecond t

theorem coreGate_deriv (t : ℝ) : deriv coreGate t = coreGateDeriv t := (coreGate_hasDerivAt t).deriv

theorem coreGateDeriv_hasDerivAt (t : ℝ) : HasDerivAt coreGateDeriv (coreGateSecond t) t := by
  have h := ((coreGateRoot_hasDerivAt t).mul (coreGateRootDeriv_hasDerivAt t)).const_mul 2
  convert h using 1
  · funext x
    unfold coreGateDeriv
    ring
  · unfold coreGateSecond
    ring

theorem coreGate_second (t : ℝ) : deriv (deriv coreGate) t = coreGateSecond t := by
  rw [show deriv coreGate = coreGateDeriv from funext coreGate_deriv]
  exact (coreGateDeriv_hasDerivAt t).deriv

theorem coreGateDeriv_nonneg (t : ℝ) : 0 ≤ coreGateDeriv t :=
  mul_nonneg (mul_nonneg (by norm_num) (coreGateRoot_nonneg t)) (coreGateRootDeriv_nonneg t)

theorem coreGateDeriv_bound (t : ℝ) : |coreGateDeriv t| ≤ 16 := by
  have h := mul_le_mul (coreGateRoot_bound t) (coreGateRootDeriv_bound t)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  unfold coreGateDeriv
  rw [abs_mul, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith only [h]

theorem coreGateSecond_bound (t : ℝ) : |coreGateSecond t| ≤ 512 := by
  have hd : coreGateRootDeriv t ^ 2 ≤ 16 := by
    have h := mul_self_le_mul_self (abs_nonneg _) (coreGateRootDeriv_bound t)
    nlinarith [sq_abs (coreGateRootDeriv t)]
  have hp := mul_le_mul (coreGateRoot_bound t) (coreGateRootSecond_bound t)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h := abs_add_le (2 * coreGateRootDeriv t ^ 2) (2 * coreGateRoot t * coreGateRootSecond t)
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * coreGateRootDeriv t ^ 2), abs_mul, abs_mul] at h
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  unfold coreGateSecond
  nlinarith only [h, hd, hp]

theorem coreGate_derivatives_flat {t : ℝ} (ht : t ≤ 1 / 2) :
    coreGateDeriv t = 0 ∧ coreGateSecond t = 0 := by
  simp only [coreGateDeriv, coreGateSecond, coreGateRoot_zero ht,
    coreGateRootDeriv_flat ht, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_add,
    and_self]

end FreshGradientMinimax
