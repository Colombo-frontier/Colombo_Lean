import GradientHessian.GaussianConcentrationHessian
import GradientHessian.GaussianConcentrationSmoothedIBP
import GradientHessian.GaussianConcentrationTimeDerivative

/-! Identification of the actual OU time derivative with the Gaussian
generator, for C2 Lipschitz functions with bounded Hessian. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal InnerProductSpace BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem smoothed_gradient_integrable {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f) (ρ σ : ℝ) (x : E) :
    Integrable (fun z => fderiv ℝ f (ρ • x + σ • z)) (euclideanGaussianLaw E) :=
  (integrable_const (B : ℝ)).mono'
    ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_fderiv_le_of_lipschitz ℝ hLip)

theorem smoothed_hessian_integrable {f : E → ℝ} {C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (ρ σ : ℝ) (x : E) :
    Integrable (fun z => fderiv ℝ (fderiv ℝ f) (ρ • x + σ • z)) (euclideanGaussianLaw E) := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  refine (integrable_const (C : ℝ)).mono'
    (f := fun z : E => fderiv ℝ (fderiv ℝ f) (ρ • x + σ • z)) ?_
    (ae_of_all _ fun z => hH (ρ • x + σ • z))
  exact (hc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable

omit [MeasurableSpace E] [BorelSpace E] in
theorem covector_basis_expansion (l : E →L[ℝ] ℝ) (z : E) :
    l z = ∑ i, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * l (stdOrthonormalBasis ℝ E i) := by
  nth_rw 1 [← (stdOrthonormalBasis ℝ E).sum_repr' z]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem smoothed_trace_ibp {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) (ρ σ : ℝ) (x : E) :
    (∫ z, fderiv ℝ f (ρ • x + σ • z) z ∂euclideanGaussianLaw E) =
      σ * ∑ i, ∫ z, diagonalSecond E f i (ρ • x + σ • z) ∂euclideanGaussianLaw E := by
  have hXi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ *
        coordinateDerivative E f i (ρ • x + σ • z)) (euclideanGaussianLaw E) := by
    have hc : Continuous (fun z => coordinateDerivative E f i (ρ • x + σ • z)) :=
      ((hf.continuous_fderiv (by norm_num)).comp
        (continuous_const.add (continuous_const.smul continuous_id))).clm_apply continuous_const
    refine ((norm_integrable E).const_mul (B : ℝ)).mono'
      ((continuous_const.inner (𝕜 := ℝ) continuous_id).mul hc).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (stdOrthonormalBasis ℝ E i) z
    rw [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_mul] at hi
    have h := mul_le_mul hi (coordinateDerivative_norm_le E hLip i (ρ • x + σ • z))
      (norm_nonneg _) (norm_nonneg z)
    simpa only [mul_comm] using h
  have he (z : E) : fderiv ℝ f (ρ • x + σ • z) z =
      ∑ i, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * coordinateDerivative E f i (ρ • x + σ • z) :=
    covector_basis_expansion E _ z
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => hXi i), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => gaussian_smoothed_coordinate_ibp E hf hLip hH ρ σ x i)

theorem mehler_generator_formula {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) (ρ : ℝ) (x : E) :
    gaussianGenerator E (mehler E ρ f) x =
      ρ ^ 2 * (∑ i, ∫ z, diagonalSecond E f i (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
        ∂euclideanGaussianLaw E) -
      ρ * (∫ z, fderiv ℝ f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) x ∂euclideanGaussianLaw E) := by
  have hI := smoothed_gradient_integrable E hf hLip ρ (Real.sqrt (1 - ρ ^ 2)) x
  have hJ := smoothed_hessian_integrable E hf hH ρ (Real.sqrt (1 - ρ ^ 2)) x
  unfold gaussianGenerator diagonalSecond
  rw [mehler_fderiv (hf.of_le (by norm_num)) hLip, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.integral_apply hI, smul_eq_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mehler_hessian hf hLip hH, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.integral_apply hJ,
    ContinuousLinearMap.integral_apply (hJ.apply_continuousLinearMap _)]

theorem ornsteinUhlenbeck_time_generator {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => ornsteinUhlenbeck E s f x)
      (gaussianGenerator E (ornsteinUhlenbeck E t f) x) t := by
  have hd := ornsteinUhlenbeck_time_hasDerivAt (hf.of_le (by norm_num)) hLip ht x
  let ρ := Real.exp (-t)
  let σ := Real.sqrt (1 - ρ ^ 2)
  have hσ : σ ≠ 0 := (Real.sqrt_pos.2 (ou_noise_positive ht)).ne'
  have hI := (smoothed_gradient_integrable E hf hLip ρ σ x).apply_continuousLinearMap x
  have hZ : Integrable (fun z => fderiv ℝ f (ρ • x + σ • z) z) (euclideanGaussianLaw E) := by
    refine ((norm_integrable E).const_mul (B : ℝ)).mono'
      (((hf.continuous_fderiv (by norm_num)).comp
        (continuous_const.add (continuous_const.smul continuous_id))).clm_apply continuous_id).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    exact ((fderiv ℝ f _).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg z))
  have he : (∫ z, fderiv ℝ f (ρ • x + σ • z) ((-ρ) • x + (ρ ^ 2 / σ) • z)
      ∂euclideanGaussianLaw E) = gaussianGenerator E (mehler E ρ f) x := by
    simp_rw [map_add, map_smul, smul_eq_mul]
    rw [integral_add (hI.const_mul (-ρ)) (hZ.const_mul (ρ ^ 2 / σ)),
      integral_const_mul, integral_const_mul, smoothed_trace_ibp E hf hLip hH,
      mehler_generator_formula E hf hLip hH]
    field_simp [hσ]
    ring
  exact he ▸ hd

end GradientHessian.GaussianConcentration
