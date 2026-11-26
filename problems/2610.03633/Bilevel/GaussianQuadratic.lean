import Bilevel.GaussianProductLaw

/-! Exact quadratic exponential moments of actual standard Gaussian draws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Bilevel.GaussianQuadratic

def inverseVariance (a : ℝ) (ha : 0 < a) : ℝ≥0 := ⟨1 / a, by positivity⟩

theorem inverseVariance_ne_zero (a : ℝ) (ha : 0 < a) : inverseVariance a ha ≠ 0 := by
  apply ne_of_gt
  change (0 : ℝ) < 1 / a
  positivity

theorem quadratic_tilt_pdf (a : ℝ) (ha : 0 < a) (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp ((1 - a) / 2 * x ^ 2) =
      Real.sqrt (1 / a) * gaussianPDFReal 0 (inverseVariance a ha) x := by
  have hexp : -x ^ 2 / 2 + (1 - a) / 2 * x ^ 2 = -x ^ 2 / (2 * (1 / a)) := by
    field_simp
    ring
  have hroot : Real.sqrt (2 * Real.pi * (1 / a)) =
      Real.sqrt (2 * Real.pi) * Real.sqrt (1 / a) := Real.sqrt_mul (by positivity) _
  simp only [gaussianPDFReal, inverseVariance, NNReal.coe_mk, NNReal.coe_one, sub_zero, mul_one]
  rw [mul_assoc, ← Real.exp_add, hexp, hroot]
  have hr : Real.sqrt (1 / a) ≠ 0 := by positivity
  field_simp

theorem weighted_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp ((1 - a) / 2 * x ^ 2)) := by
  simp_rw [quadratic_tilt_pdf a ha]
  exact (integrable_gaussianPDFReal 0 (inverseVariance a ha)).const_mul _

theorem quadratic_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp ((1 - a) / 2 * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))).mpr
  simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul] using
    weighted_integrable a ha

theorem quadratic_moment (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, Real.exp ((1 - a) / 2 * x ^ 2) ∂gaussianReal 0 1) = Real.sqrt (1 / a) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  simp_rw [quadratic_tilt_pdf a ha]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 (inverseVariance_ne_zero a ha), mul_one]

def quadraticProduct (n : ℕ) (a : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, Real.exp ((1 - a i) / 2 * (x i) ^ 2)

theorem product_density_identity (n : ℕ) (a : Fin n → ℝ) (x : Fin n → ℝ) :
    GaussianAffinity.density n 0 1 x * quadraticProduct n a x =
      ∏ i, (gaussianPDFReal 0 1 (x i) * Real.exp ((1 - a i) / 2 * (x i) ^ 2)) := by
  simp only [GaussianAffinity.density, quadraticProduct, Finset.prod_mul_distrib]

theorem product_integrable (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    Integrable (quadraticProduct n a) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  rw [GaussianProductLaw.gaussian_pi_eq_withDensity n 0 1 (by norm_num)]
  apply (integrable_withDensity_iff_integrable_smul'
    (GaussianProductLaw.density_measurable n 0 1).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp only [ENNReal.toReal_ofReal (GaussianAffinity.density_nonnegative n 0 1 _), smul_eq_mul]
  simp_rw [product_density_identity]
  exact Integrable.fintype_prod (fun i => weighted_integrable (a i) (ha i))

theorem product_moment (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x, quadraticProduct n a x ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∏ i, Real.sqrt (1 / a i) := by
  rw [GaussianProductLaw.integral_gaussian_pi_eq n 0 1 (by norm_num)]
  simp only [smul_eq_mul]
  simp_rw [product_density_identity]
  rw [integral_fintype_prod_eq_prod (Fin n)
    (fun i (z : ℝ) => gaussianPDFReal 0 1 z * Real.exp ((1 - a i) / 2 * z ^ 2))]
  apply Finset.prod_congr rfl
  intro i _
  have h := quadratic_moment (a i) (ha i)
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)] at h
  simpa only [smul_eq_mul] using h

end Bilevel.GaussianQuadratic
