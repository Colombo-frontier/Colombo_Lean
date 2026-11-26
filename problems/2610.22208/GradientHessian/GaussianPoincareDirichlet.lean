import GradientHessian.GaussianConcentrationDirichlet
import GradientHessian.GaussianConcentrationSmoothedIBP

/-! Growth hypotheses for the Gaussian Dirichlet identity are discharged
from bounded values and bounded first two derivatives. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal InnerProductSpace BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_bounded_integrable {f : E → ℝ} (hf : Continuous f) {D : ℝ}
    (hD : ∀ x, ‖f x‖ ≤ D) : Integrable f (euclideanGaussianLaw E) :=
  (integrable_const D).mono' hf.aestronglyMeasurable (ae_of_all _ hD)

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_generator_continuous {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (gaussianGenerator E f) := by
  have h1 := hf.continuous_fderiv (by norm_num)
  have h2 := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  exact (continuous_finset_sum _ (fun i _ =>
    (h2.clm_apply continuous_const).clm_apply continuous_const)).sub
    (h1.clm_apply continuous_id)

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_generator_norm_le {f : E → ℝ} {B C : ℝ≥0}
    (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) (x : E) :
    ‖gaussianGenerator E f x‖ ≤ (Module.finrank ℝ E : ℝ) * C + B * ‖x‖ := by
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · calc
      ‖∑ i, diagonalSecond E f i x‖ ≤ ∑ i, ‖diagonalSecond E f i x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (Module.finrank ℝ E), (C : ℝ) :=
        Finset.sum_le_sum (fun i _ => diagonalSecond_norm_le E hH i x)
      _ = _ := by simp
  · exact ((fderiv ℝ f x).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg x))

theorem gaussian_dirichlet_bounded_self {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) :
    (∫ x, f x * gaussianGenerator E f x ∂euclideanGaussianLaw E) =
      -(∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂euclideanGaussianLaw E) := by
  have hDn : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hc1 (i) : Continuous (coordinateDerivative E f i) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hc2 (i) : Continuous (diagonalSecond E f i) :=
    (((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have h0 (i) : Integrable (fun x => f x * coordinateDerivative E f i x)
      (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E (hf.continuous.mul (hc1 i))
    intro x
    rw [norm_mul]
    exact mul_le_mul (hD x) (coordinateDerivative_norm_le E hLip i x) (norm_nonneg _) hDn
  have h1 (i) : Integrable (fun x => (coordinateDerivative E f i x) ^ 2)
      (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E ((hc1 i).pow 2)
    intro x
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (coordinateDerivative_norm_le E hLip i x) 2
  have h2 (i) : Integrable (fun x => f x * diagonalSecond E f i x)
      (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E (hf.continuous.mul (hc2 i))
    intro x
    rw [norm_mul]
    exact mul_le_mul (hD x) (diagonalSecond_norm_le E hH i x) (norm_nonneg _) hDn
  have hX (i) : Integrable (fun x => ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ *
      (f x * coordinateDerivative E f i x)) (euclideanGaussianLaw E) := by
    refine ((norm_integrable E).mul_const (D * B)).mono'
      ((continuous_const.inner (𝕜 := ℝ) continuous_id).mul
        (hf.continuous.mul (hc1 i))).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [norm_mul, norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (stdOrthonormalBasis ℝ E i) x
    rw [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_mul] at hi
    exact mul_le_mul hi
      (mul_le_mul (hD x) (coordinateDerivative_norm_le E hLip i x) (norm_nonneg _) hDn)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  exact gaussian_dirichlet_self E hf h0 h1 h2 hX

end GradientHessian.GaussianConcentration
