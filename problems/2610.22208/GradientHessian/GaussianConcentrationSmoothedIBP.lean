import GradientHessian.GaussianConcentrationGenerator
import GradientHessian.GaussianConcentrationDerivative

/-! Gaussian integration by parts for the actual smoothed first derivative.
All growth conditions are discharged from global first and second derivative
bounds; no integration-by-parts or generator identity is assumed. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem coordinateDerivative_norm_le {f : E → ℝ} {B : ℝ≥0} (hf : LipschitzWith B f)
    (i : Fin (Module.finrank ℝ E)) (x : E) : ‖coordinateDerivative E f i x‖ ≤ (B : ℝ) := by
  have he := (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i
  have h := (fderiv ℝ f x).le_opNorm (stdOrthonormalBasis ℝ E i)
  rw [he, mul_one] at h
  exact h.trans (norm_fderiv_le_of_lipschitz ℝ hf)

omit [MeasurableSpace E] [BorelSpace E] in
theorem diagonalSecond_norm_le {f : E → ℝ} {C : ℝ≥0}
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (i : Fin (Module.finrank ℝ E)) (x : E) : ‖diagonalSecond E f i x‖ ≤ (C : ℝ) := by
  have he := (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i
  have h1 := (fderiv ℝ (fderiv ℝ f) x).le_opNorm (stdOrthonormalBasis ℝ E i)
  have h2 := (fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i)).le_opNorm
    (stdOrthonormalBasis ℝ E i)
  rw [he, mul_one] at h1 h2
  exact h2.trans (h1.trans (hH x))

theorem gaussian_smoothed_coordinate_ibp {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (ρ σ : ℝ) (x : E) (i : Fin (Module.finrank ℝ E)) :
    (∫ z, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * coordinateDerivative E f i (ρ • x + σ • z)
      ∂euclideanGaussianLaw E) =
      σ * ∫ z, diagonalSecond E f i (ρ • x + σ • z) ∂euclideanGaussianLaw E := by
  let g : E → ℝ := fun z => coordinateDerivative E f i (ρ • x + σ • z)
  have hd (z : E) : HasFDerivAt g
      (((fderiv ℝ (fderiv ℝ f) (ρ • x + σ • z)).flip (stdOrthonormalBasis ℝ E i)).comp
        (σ • ContinuousLinearMap.id ℝ E)) z :=
    (partial_hasFDerivAt E hf i _).comp z
      (((hasFDerivAt_id (𝕜 := ℝ) z).const_smul σ).const_add (ρ • x))
  have he (z : E) : fderiv ℝ g z (stdOrthonormalBasis ℝ E i) =
      σ * diagonalSecond E f i (ρ • x + σ • z) := by
    rw [(hd z).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul,
      diagonalSecond]
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr (fun z => (hd z).continuousAt)
  have hgc : Integrable g (euclideanGaussianLaw E) :=
    (integrable_const (B : ℝ)).mono' hgcont.aestronglyMeasurable
      (ae_of_all _ fun z => coordinateDerivative_norm_le E hLip i _)
  have hdc : Continuous (fun z => diagonalSecond E f i (ρ • x + σ • z)) := by
    have hc : Continuous (fderiv ℝ (fderiv ℝ f)) :=
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
    exact ((hc.comp (continuous_const.add (continuous_const.smul continuous_id))).clm_apply
      continuous_const).clm_apply continuous_const
  have hdi : Integrable (fun z => diagonalSecond E f i (ρ • x + σ • z))
      (euclideanGaussianLaw E) :=
    (integrable_const (C : ℝ)).mono' hdc.aestronglyMeasurable
      (ae_of_all _ fun z => diagonalSecond_norm_le E hH i _)
  have hD : Integrable (fun z => fderiv ℝ g z (stdOrthonormalBasis ℝ E i))
      (euclideanGaussianLaw E) := by
    simp_rw [he]
    exact hdi.const_mul σ
  have hX : Integrable (fun z => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * g z)
      (euclideanGaussianLaw E) := by
    refine ((norm_integrable E).const_mul (B : ℝ)).mono'
      ((continuous_const.inner (𝕜 := ℝ) continuous_id).mul hgcont).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (stdOrthonormalBasis ℝ E i) z
    rw [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_mul] at hi
    have h := mul_le_mul hi (coordinateDerivative_norm_le E hLip i (ρ • x + σ • z))
      (norm_nonneg (g z)) (norm_nonneg z)
    simpa only [mul_comm] using h
  have h := hilbert_gaussian_integration_by_parts E i (fun z => (hd z).differentiableAt) hgc hD hX
  simp_rw [he] at h
  rw [integral_const_mul] at h
  exact h

end GradientHessian.GaussianConcentration
