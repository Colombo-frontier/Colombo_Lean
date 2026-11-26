import GradientHessian.IntegralProfiles

noncomputable section
namespace GradientHessian.LatchProfiles

open Profiles IntegralProfiles

theorem chi_derivative_nonneg (u : ℝ) : 0 ≤ deriv chi u := by
  rw [(chi_derivative u).deriv]
  have h := (derivative_bounds (4 * u - 1)).1
  rw [deriv_step] at h
  positivity

theorem chi_derivative_support {u : ℝ} (hu : 0 < deriv chi u) :
    1 / 4 < u ∧ u < 1 / 2 := by
  rw [(chi_derivative u).deriv] at hu
  have hflat : ∀ x : ℝ, x ≤ 0 ∨ 1 ≤ x → step₁ x = 0 := by
    intro x hx
    simpa only [deriv_step] using (derivatives_flat_outside hx).1
  constructor
  · by_contra h
    have he := hflat (4 * u - 1) (Or.inl (by linarith))
    rw [he] at hu
    linarith
  · by_contra h
    have he := hflat (4 * u - 1) (Or.inr (by linarith))
    rw [he] at hu
    linarith

theorem chi_derivative_zero_of_ge {u : ℝ} (hu : 1 / 2 ≤ u) : deriv chi u = 0 := by
  have h := (derivatives_flat_outside (Or.inr (by linarith : 1 ≤ 4 * u - 1))).1
  rw [deriv_step] at h
  rw [(chi_derivative u).deriv, h, mul_zero]

theorem varpi_derivative (u : ℝ) :
    HasDerivAt varpi (12 * step₁ (12 * (u - 2 / 3))) u := by
  convert (step_derivative (12 * (u - 2 / 3))).comp u
    (((hasDerivAt_id u).sub_const (2 / 3)).const_mul 12) using 1
  simp [varpi, mul_comm]

theorem varpi_derivative_nonneg (u : ℝ) : 0 ≤ deriv varpi u := by
  rw [(varpi_derivative u).deriv]
  have h := (derivative_bounds (12 * (u - 2 / 3))).1
  rw [deriv_step] at h
  positivity

theorem varpi_derivative_support {u : ℝ} (hu : 0 < deriv varpi u) :
    2 / 3 < u ∧ u < 3 / 4 := by
  rw [(varpi_derivative u).deriv] at hu
  have hflat : ∀ x : ℝ, x ≤ 0 ∨ 1 ≤ x → step₁ x = 0 := by
    intro x hx
    simpa only [deriv_step] using (derivatives_flat_outside hx).1
  constructor
  · by_contra h
    have he := hflat (12 * (u - 2 / 3)) (Or.inl (by linarith))
    rw [he] at hu
    linarith
  · by_contra h
    have he := hflat (12 * (u - 2 / 3)) (Or.inr (by linarith))
    rw [he] at hu
    linarith

theorem ell₀_derivative_identity {u : ℝ} (hu : |u| ≤ 2) : deriv ell₀ u = 1 := by
  rw [(ell₀_derivative u).deriv, step_nonpos (by linarith), sub_zero]

end GradientHessian.LatchProfiles
