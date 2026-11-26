import GradientHessian.SphereMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.SubGaussian

/-!
# The sharp spherical moment generating function and tail

These are statements about `SphereGaussian.sphereLaw`, the actual normalized
Gaussian measure.  The sharp coefficient is the ambient dimension `m`.
-/

namespace GradientHessian.SharpSphereTail

open MeasureTheory ProbabilityTheory Filter
open GradientHessian.GaussianHilbert GradientHessian.SphereGaussian
open GradientHessian.SphereMoments
open scoped InnerProductSpace ENNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem sphere_exp_inner_integrable (y : E) :
    Integrable (fun x => Real.exp ⟪y,x⟫_ℝ) (sphereLaw E) := by
  refine (integrable_const (Real.exp ‖y‖)).mono'
    (show Continuous (fun x : E => Real.exp ⟪y,x⟫_ℝ) by fun_prop).aestronglyMeasurable ?_
  filter_upwards [sphereLaw_unit (E := E)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by simpa [hx] using abs_real_inner_le_norm y x)

omit [Nontrivial E] in
theorem sphere_exp_inner_neg (y : E) :
    (∫ x, Real.exp (-⟪y,x⟫_ℝ) ∂sphereLaw E) =
      ∫ x, Real.exp ⟪y,x⟫_ℝ ∂sphereLaw E := by
  let U := LinearIsometryEquiv.neg ℝ (E := E)
  have hp : MeasurePreserving U (sphereLaw E) (sphereLaw E) :=
    ⟨U.continuous.measurable, sphereLaw_isometry U⟩
  simpa only [U, LinearIsometryEquiv.coe_neg, inner_neg_right] using
    hp.integral_comp U.toHomeomorph.measurableEmbedding (fun x => Real.exp ⟪y,x⟫_ℝ)

theorem sphere_cosh_inner_integrable (y : E) :
    Integrable (fun x => Real.cosh ⟪y,x⟫_ℝ) (sphereLaw E) := by
  simpa only [Real.cosh_eq, inner_neg_left] using
    ((sphere_exp_inner_integrable y).add (sphere_exp_inner_integrable (-y))).div_const 2

theorem sphere_cosh_inner_eq_exp (y : E) :
    (∫ x, Real.cosh ⟪y,x⟫_ℝ ∂sphereLaw E) =
      ∫ x, Real.exp ⟪y,x⟫_ℝ ∂sphereLaw E := by
  have hn : Integrable (fun x => Real.exp (-⟪y,x⟫_ℝ)) (sphereLaw E) := by
    simpa only [inner_neg_left] using sphere_exp_inner_integrable (-y)
  simp_rw [Real.cosh_eq]
  rw [integral_div, integral_add (sphere_exp_inner_integrable y) hn, sphere_exp_inner_neg]
  ring

omit [Nontrivial E] in
theorem gaussian_cosh_inner_integrable (y : E) :
    Integrable (fun x => Real.cosh ⟪y,x⟫_ℝ) (euclideanGaussianLaw E) := by
  simpa only [Real.cosh_eq, inner_neg_left] using
    ((euclideanGaussian_exp_inner_integrable E y).add
      (euclideanGaussian_exp_inner_integrable E (-y))).div_const 2

omit [Nontrivial E] in
theorem gaussian_cosh_inner (y : E) :
    (∫ x, Real.cosh ⟪y,x⟫_ℝ ∂euclideanGaussianLaw E) = Real.exp (‖y‖^2/2) := by
  have hn : Integrable (fun x => Real.exp (-⟪y,x⟫_ℝ)) (euclideanGaussianLaw E) := by
    simpa only [inner_neg_left] using euclideanGaussian_exp_inner_integrable E (-y)
  have hnval : (∫ x, Real.exp (-⟪y,x⟫_ℝ) ∂euclideanGaussianLaw E) = Real.exp (‖y‖^2/2) := by
    simpa only [inner_neg_left, norm_neg] using euclideanGaussian_exp_inner E (-y)
  simp_rw [Real.cosh_eq]
  rw [integral_div, integral_add (euclideanGaussian_exp_inner_integrable E y) hn,
    euclideanGaussian_exp_inner, hnval]
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E] in
theorem lintegral_cosh_series (μ : Measure E) (f : E → ℝ) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (Real.cosh (f x)) ∂μ) =
      ∑' q : ℕ, ∫⁻ x, ENNReal.ofReal ((f x)^(2*q)/(2*q).factorial) ∂μ := by
  have he (x : E) : ENNReal.ofReal (Real.cosh (f x)) =
      ∑' q : ℕ, ENNReal.ofReal ((f x)^(2*q)/(2*q).factorial) := by
    rw [Real.cosh_eq_tsum]
    exact ENNReal.ofReal_tsum_of_nonneg (fun q => by rw [pow_mul]; positivity)
      (Real.hasSum_cosh (f x)).summable
  simp_rw [he]
  exact lintegral_tsum (fun q => ((hf.pow_const _).div_const _).ennreal_ofReal.aemeasurable)

theorem sphere_cosh_inner_le_gaussian (y : E) :
    (∫ x, Real.cosh ⟪y,x⟫_ℝ ∂sphereLaw E) ≤
      ∫ x, Real.cosh ⟪(Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ • y,x⟫_ℝ
        ∂euclideanGaussianLaw E := by
  let z := (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ • y
  have hc : (∫⁻ x, ENNReal.ofReal (Real.cosh ⟪y,x⟫_ℝ) ∂sphereLaw E) ≤
      ∫⁻ x, ENNReal.ofReal (Real.cosh ⟪z,x⟫_ℝ) ∂euclideanGaussianLaw E := by
    rw [lintegral_cosh_series _ _ (by fun_prop), lintegral_cosh_series _ _ (by fun_prop)]
    apply ENNReal.tsum_le_tsum
    intro q
    have hn (v : E) (x : E) : 0 ≤ ⟪v,x⟫_ℝ^(2*q)/(2*q).factorial := by
      rw [pow_mul]; positivity
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((sphere_inner_pow_integrable y (2*q)).div_const _) (ae_of_all _ (hn y)),
      ← ofReal_integral_eq_lintegral_ofReal
      ((gaussian_inner_even_integrable z q).div_const _) (ae_of_all _ (hn z)),
      integral_div, integral_div]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (sphere_even_moment_le_scaled_gaussian y q) (Nat.cast_nonneg _))
  rw [← ofReal_integral_eq_lintegral_ofReal (sphere_cosh_inner_integrable y)
    (ae_of_all _ fun _ => (Real.cosh_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal (gaussian_cosh_inner_integrable z)
    (ae_of_all _ fun _ => (Real.cosh_pos _).le)] at hc
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => (Real.cosh_pos _).le)).mp hc

/-- Exact source spherical exponential moment, with coefficient `1/m`. -/
theorem sphere_exp_inner_le (y : E) :
    (∫ x, Real.exp ⟪y,x⟫_ℝ ∂sphereLaw E) ≤
      Real.exp (‖y‖^2/(2*(Module.finrank ℝ E : ℝ))) := by
  rw [← sphere_cosh_inner_eq_exp]
  have h := sphere_cosh_inner_le_gaussian y
  rw [gaussian_cosh_inner] at h
  convert h using 1
  congr 1
  have hm : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hm]
  ring

theorem sphereLaw_mgf_inner (y : E) (t : ℝ) :
    (∫ x, Real.exp (t*⟪y,x⟫_ℝ) ∂sphereLaw E) ≤
      Real.exp (t^2*‖y‖^2/(2*(Module.finrank ℝ E : ℝ))) := by
  simpa only [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
    sphere_exp_inner_le (t • y)

theorem sphereLaw_hasSubgaussianMGF (y : E) :
    HasSubgaussianMGF (fun x => ⟪y,x⟫_ℝ)
      ⟨‖y‖^2/(Module.finrank ℝ E : ℝ), by positivity⟩ (sphereLaw E) where
  integrable_exp_mul t := by
    simpa only [real_inner_smul_left] using sphere_exp_inner_integrable (t • y)
  mgf_le t := by
    have h := sphereLaw_mgf_inner y t
    convert h using 1
    congr 1
    simp only [NNReal.coe_mk]
    ring

theorem sphereLaw_right_tail (y : E) (hy : y ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (sphereLaw E).real {x | t ≤ ⟪y,x⟫_ℝ} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ)*t^2/(2*‖y‖^2)) := by
  have h := (sphereLaw_hasSubgaussianMGF y).measure_ge_le ht
  convert h using 1
  congr 1
  simp only [NNReal.coe_mk]
  have hm : (Module.finrank ℝ E : ℝ) ≠ 0 := (Nat.cast_pos.mpr Module.finrank_pos).ne'
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  field_simp
  ring

/-- The literal sharp two-sided tail from source `eq:sphere`.
The threshold is nonnegative and the test vector is nonzero. -/
theorem sphereLaw_sharp_tail (y : E) (hy : y ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (sphereLaw E).real {x | t ≤ |⟪y,x⟫_ℝ|} ≤
      2*Real.exp (-(Module.finrank ℝ E : ℝ)*t^2/(2*‖y‖^2)) := by
  have hs : {x : E | t ≤ |⟪y,x⟫_ℝ|} ⊆
      {x | t ≤ ⟪y,x⟫_ℝ} ∪ {x | t ≤ ⟪-y,x⟫_ℝ} := by
    intro x hx
    change t ≤ |⟪y,x⟫_ℝ| at hx
    rcases le_abs.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [inner_neg_left] using h)
  have hp := sphereLaw_right_tail y hy ht
  have hn := sphereLaw_right_tail (-y) (neg_ne_zero.mpr hy) ht
  rw [norm_neg] at hn
  calc
    _ ≤ (sphereLaw E).real ({x | t ≤ ⟪y,x⟫_ℝ} ∪ {x | t ≤ ⟪-y,x⟫_ℝ}) := measureReal_mono hs
    _ ≤ (sphereLaw E).real {x | t ≤ ⟪y,x⟫_ℝ} + (sphereLaw E).real {x | t ≤ ⟪-y,x⟫_ℝ} :=
      measureReal_union_le _ _
    _ ≤ _ := by linarith

end
end GradientHessian.SharpSphereTail
