import FreshGradientMinimax.CompressionSecond

/-! The paper's radial compression at any positive radius, including its
actual derivative and the global constants one and three over the radius. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialCompression (R : ℝ) (x : E) : E := R • unitCompression (R⁻¹ • x)

def radialCompressionDerivative (R : ℝ) (x : E) : E →L[ℝ] E :=
  unitCompressionDerivative (R⁻¹ • x)

theorem radialCompression_formula {R : ℝ} (hR : 0 < R) (x : E) :
    radialCompression R x = (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ • x := by
  simp only [radialCompression, unitCompression, compressionFactor, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hR, mul_pow, inv_pow, ← div_eq_inv_mul, smul_smul]
  congr 1
  field_simp

theorem radialCompression_contDiff {m : ℕ∞} (R : ℝ) : ContDiff ℝ m (radialCompression R : E → E) :=
  (unitCompression_contDiff.comp (contDiff_const.smul contDiff_id)).const_smul R

theorem radialCompression_hasFDerivAt {R : ℝ} (hR : 0 < R) (x : E) :
    HasFDerivAt (radialCompression R) (radialCompressionDerivative R x) x := by
  apply (((unitCompression_hasFDerivAt (R⁻¹ • x)).comp x
    ((hasFDerivAt_id x).const_smul R⁻¹)).const_smul R).congr_fderiv
  ext v
  simp only [radialCompressionDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul, smul_smul,
    mul_inv_cancel₀ hR.ne', one_smul]

theorem radialCompressionDerivative_norm {R : ℝ} (x : E) :
    ‖radialCompressionDerivative R x‖ ≤ 1 := unitCompressionDerivative_norm _

theorem radialCompressionDerivative_norm_apply {R : ℝ} (x v : E) :
    ‖radialCompressionDerivative R x v‖ ≤ ‖v‖ := by
  have h := mul_le_mul_of_nonneg_right (radialCompressionDerivative_norm (R := R) x) (norm_nonneg v)
  exact ((radialCompressionDerivative R x).le_opNorm v).trans (by simpa only [one_mul] using h)

theorem radialCompressionDerivative_selfAdjoint (R : ℝ) (x v w : E) :
    ⟪radialCompressionDerivative R x v, w⟫_ℝ = ⟪v, radialCompressionDerivative R x w⟫_ℝ :=
  unitCompressionDerivative_selfAdjoint _ _ _

theorem radialCompression_norm_bound {R : ℝ} (hR : 0 ≤ R) (x : E) :
    ‖radialCompression R x‖ ≤ R := by
  rw [radialCompression, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
  exact mul_le_of_le_one_right hR (unitCompression_norm_le_one _)

theorem radialCompression_sub_norm {R : ℝ} (hR : 0 < R) (x y : E) :
    ‖radialCompression R x - radialCompression R y‖ ≤ ‖x - y‖ := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (radialCompression_hasFDerivAt hR z).hasFDerivWithinAt)
    (fun z _ => radialCompressionDerivative_norm z) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [one_mul] using h

theorem radialCompressionDerivative_sub_norm {R : ℝ} (hR : 0 < R) (x y : E) :
    ‖radialCompressionDerivative R x - radialCompressionDerivative R y‖ ≤ 3 / R * ‖x - y‖ := by
  have h := unitCompressionDerivative_sub_norm (R⁻¹ • x) (R⁻¹ • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR] at h
  simpa only [radialCompressionDerivative, div_eq_mul_inv, mul_assoc] using h

theorem radialCompression_zero (R : ℝ) : radialCompression R (0 : E) = 0 := by
  simp only [radialCompression, smul_zero, unitCompression_zero]

theorem radialCompression_fderiv {R : ℝ} (hR : 0 < R) (x : E) :
    fderiv ℝ (radialCompression R) x = radialCompressionDerivative R x :=
  (radialCompression_hasFDerivAt hR x).fderiv

theorem radialCompression_second_fderiv_bound {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (radialCompression R : E → E)) x‖ ≤ 3 / R := by
  have hl : LipschitzWith ⟨3 / R, by positivity⟩ (radialCompressionDerivative R : E → E →L[ℝ] E) :=
    lipschitzWith_iff_norm_sub_le.mpr (radialCompressionDerivative_sub_norm hR)
  rw [show fderiv ℝ (radialCompression R : E → E) = radialCompressionDerivative R from
    funext (radialCompression_fderiv hR)]
  exact norm_fderiv_le_of_lipschitz ℝ hl

end FreshGradientMinimax
