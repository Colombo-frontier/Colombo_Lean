import GradientHessian.LatchGeometry
import GradientHessian.LatchProfiles

/-! Activation for the actual local register potential. The coefficients of
the neighbouring self gate and outgoing completion port are nonnegative. -/

noncomputable section
namespace GradientHessian.LatchActivation

open scoped InnerProductSpace
open RadialSquash LatchGeometry LatchProfiles Profiles IntegralProfiles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def readout (v z : E) : ℝ := ⟪v, squash 8 z⟫_ℝ

def potential (v : E) (d l : ℝ) (z : E) : ℝ :=
  4 * ‖z‖ ^ 2 - 8 * ell₀ (readout v z) - d * chi (readout v z) - l * varpi (readout v z)

def force (v : E) (d l : ℝ) (z : E) : E :=
  (8 : ℝ) • z -
    (8 * deriv ell₀ (readout v z) + d * deriv chi (readout v z) +
      l * deriv varpi (readout v z)) • fderiv ℝ (squash 8) z v

theorem force_activation_no_output (v z : E) (hv : ‖v‖ = 1) {d : ℝ} (hd : 0 ≤ d)
    (hf : ‖force v d 0 z‖ ≤ 1) : 7 / 8 ≤ readout v z := by
  have hc0 := chi_derivative_nonneg (readout v z)
  have he0 := (ell₀_derivative_bounds (readout v z)).1
  have he1 := (ell₀_derivative_bounds (readout v z)).2
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  by_cases hc : deriv chi (readout v z) = 0
  · have hfs : force v d 0 z = (8 : ℝ) • z -
        (8 * deriv ell₀ (readout v z)) • fderiv ℝ (squash 8) z v := by simp [force, hc]
    have hD : ‖fderiv ℝ (squash 8) z v‖ ≤ 1 := by
      have h := (fderiv ℝ (squash 8) z).le_opNorm v
      rw [hv, mul_one] at h
      exact h.trans (squash_fderiv_norm_le (by norm_num) z)
    have hterm : ‖(8 * deriv ell₀ (readout v z)) • fderiv ℝ (squash 8) z v‖ ≤ 8 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith only [he0, he1, hD, norm_nonneg (fderiv ℝ (squash 8) z v)]
    have hz8 : ‖z‖ ≤ 9 / 8 := by
      have h := norm_add_le (force v d 0 z)
        ((8 * deriv ell₀ (readout v z)) • fderiv ℝ (squash 8) z v)
      rw [hfs, sub_add_cancel, norm_smul, Real.norm_eq_abs] at h
      norm_num at h
      rw [← hfs] at h
      linarith
    have hz : ‖z‖ < 8 := by linarith
    have hu : readout v z = ⟪v, z⟫_ℝ := by
      rw [readout, squash_identity (by norm_num) hz.le]
    have hinner := norm_inner_le_norm (𝕜 := ℝ) v z
    rw [Real.norm_eq_abs, hv, one_mul, ← hu] at hinner
    have he : deriv ell₀ (readout v z) = 1 :=
      ell₀_derivative_identity (by linarith)
    rw [hfs, he, squash_fderiv_identity (by norm_num) z hz,
      ContinuousLinearMap.id_apply] at hf
    have hi := norm_inner_le_norm (𝕜 := ℝ) v ((8 : ℝ) • z - ((8 : ℝ) * 1) • v)
    rw [Real.norm_eq_abs, hv, one_mul] at hi
    have h := (abs_le.mp (hi.trans hf)).1
    simp only [inner_sub_right, real_inner_smul_right, hvv, mul_one, ← hu] at h
    linarith
  · have hcpos : 0 < deriv chi (readout v z) := lt_of_le_of_ne hc0 (Ne.symm hc)
    obtain ⟨hu0, hu1⟩ := chi_derivative_support hcpos
    have hfs : force v d 0 z = (8 : ℝ) • z -
        (8 * deriv ell₀ (readout v z) + d * deriv chi (readout v z)) •
          fderiv ℝ (squash 8) z v := by simp [force]
    have hf' := hf
    rw [hfs] at hf'
    have hz := positive_readout_force_inside v z hv
      (add_nonneg (mul_nonneg (by norm_num) he0) (mul_nonneg hd hc0))
      (by change 0 < readout v z; linarith) (by change readout v z < 1; linarith) hf'
    have hu : readout v z = ⟪v, z⟫_ℝ := by
      rw [readout, squash_identity (by norm_num) hz.le]
    have he : deriv ell₀ (readout v z) = 1 :=
      ell₀_derivative_identity (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [he, squash_fderiv_identity (by norm_num) z hz, ContinuousLinearMap.id_apply] at hf'
    have hi := norm_inner_le_norm (𝕜 := ℝ) v
      ((8 : ℝ) • z - (8 * 1 + d * deriv chi (readout v z)) • v)
    rw [Real.norm_eq_abs, hv, one_mul] at hi
    have h := (abs_le.mp (hi.trans hf')).1
    simp only [inner_sub_right, real_inner_smul_right, hvv, mul_one, ← hu] at h
    nlinarith only [h, hu1, mul_nonneg hd hc0]

theorem force_activation (v z : E) (hv : ‖v‖ = 1) {d l : ℝ}
    (hd : 0 ≤ d) (hl : 0 ≤ l) (hf : ‖force v d l z‖ ≤ 1) :
    7 / 8 ≤ readout v z ∧ varpi (readout v z) = 1 := by
  have hport : deriv varpi (readout v z) = 0 := by
    by_contra hp
    have hpp : 0 < deriv varpi (readout v z) :=
      lt_of_le_of_ne (varpi_derivative_nonneg _) (Ne.symm hp)
    obtain ⟨hu0, hu1⟩ := varpi_derivative_support hpp
    have hc := chi_derivative_zero_of_ge (by linarith : 1 / 2 ≤ readout v z)
    have he : deriv ell₀ (readout v z) = 1 :=
      ell₀_derivative_identity (abs_le.mpr ⟨by linarith, by linarith⟩)
    have heq : force v d l z = (8 : ℝ) • z -
        (8 - (-(l * deriv varpi (readout v z)))) • fderiv ℝ (squash 8) z v := by
      simp [force, hc, he]
    have h := transition_exclusion v z hv
      (by nlinarith [mul_nonneg hl hpp.le] : -(l * deriv varpi (readout v z)) ≤ 1 / 2)
      hu0 hu1
    rw [← heq] at h
    linarith
  have hforce : force v d l z = force v d 0 z := by simp [force, hport]
  rw [hforce] at hf
  have hu := force_activation_no_output v z hv hd hf
  exact ⟨hu, varpi_one (by linarith)⟩

variable [CompleteSpace E]

theorem potential_hasGradientAt (v z : E) (d l : ℝ) :
    HasGradientAt (potential v d l) (force v d l z) z := by
  have hu := readout_hasGradientAt (by norm_num : (0 : ℝ) < 8) v z
  have he := (ell₀_derivative (readout v z)).differentiableAt.hasDerivAt.comp_hasFDerivAt z hu.hasFDerivAt
  have hc := (chi_derivative (readout v z)).differentiableAt.hasDerivAt.comp_hasFDerivAt z hu.hasFDerivAt
  have hp := (varpi_derivative (readout v z)).differentiableAt.hasDerivAt.comp_hasFDerivAt z hu.hasFDerivAt
  have hn := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (4 : ℝ)
  have h := ((hn.sub (he.const_mul 8)).sub (hc.const_mul d)).sub (hp.const_mul l)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext w
  simp [force, readout, InnerProductSpace.toDual_apply, real_inner_smul_left,
    inner_sub_left, two_smul]
  ring

/-- Activation of the literal local scalar objective, including its outgoing port. -/
theorem potential_activation (v z : E) (hv : ‖v‖ = 1) {d l : ℝ}
    (hd : 0 ≤ d) (hl : 0 ≤ l) (hg : ‖gradient (potential v d l) z‖ ≤ 1) :
    7 / 8 ≤ readout v z ∧ varpi (readout v z) = 1 := by
  rw [(potential_hasGradientAt v z d l).gradient] at hg
  exact force_activation v z hv hd hl hg

end GradientHessian.LatchActivation
