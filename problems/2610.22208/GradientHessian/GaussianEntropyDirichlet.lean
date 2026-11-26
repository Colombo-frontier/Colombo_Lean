import GradientHessian.GaussianPoincareDirichlet

/-! Gaussian integration by parts against a bounded C1 weight. These
growth conditions will be discharged for the entropy weight 1 + log g. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal InnerProductSpace BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_dirichlet_bounded_weight {u v : E → ℝ} {B C : ℝ≥0} {A U : ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hLip : LipschitzWith B v)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ (C : ℝ))
    (hA : ∀ x, ‖u x‖ ≤ A) (hU : ∀ x, ‖fderiv ℝ u x‖ ≤ U) :
    (∫ x, u x * gaussianGenerator E v x ∂euclideanGaussianLaw E) =
      -(∫ x, ∑ i, coordinateDerivative E u i x * coordinateDerivative E v i x
        ∂euclideanGaussianLaw E) := by
  have hAn : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hUn : 0 ≤ U := (norm_nonneg _).trans (hU 0)
  have hcu (i) : Continuous (coordinateDerivative E u i) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcv (i) : Continuous (coordinateDerivative E v i) :=
    (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcv2 (i) : Continuous (diagonalSecond E v i) :=
    (((hv.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv
      (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hdu (i) (x : E) : ‖coordinateDerivative E u i x‖ ≤ U := by
    have h := (fderiv ℝ u x).le_opNorm (stdOrthonormalBasis ℝ E i)
    rw [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, mul_one] at h
    exact h.trans (hU x)
  have h0 (i) : Integrable (fun x => u x * coordinateDerivative E v i x)
      (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E (hu.continuous.mul (hcv i))
    intro x
    rw [norm_mul]
    exact mul_le_mul (hA x) (coordinateDerivative_norm_le E hLip i x) (norm_nonneg _) hAn
  have h1 (i) : Integrable (fun x => coordinateDerivative E u i x * coordinateDerivative E v i x)
      (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E ((hcu i).mul (hcv i))
    intro x
    rw [norm_mul]
    exact mul_le_mul (hdu i x) (coordinateDerivative_norm_le E hLip i x) (norm_nonneg _) hUn
  have h2 (i) : Integrable (fun x => u x * diagonalSecond E v i x)
      (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E (hu.continuous.mul (hcv2 i))
    intro x
    rw [norm_mul]
    exact mul_le_mul (hA x) (diagonalSecond_norm_le E hH i x) (norm_nonneg _) hAn
  have hX (i) : Integrable (fun x => ⟪stdOrthonormalBasis ℝ E i, x⟫_ℝ *
      (u x * coordinateDerivative E v i x)) (euclideanGaussianLaw E) := by
    refine ((norm_integrable E).mul_const (A * B)).mono'
      ((continuous_const.inner (𝕜 := ℝ) continuous_id).mul
        (hu.continuous.mul (hcv i))).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [norm_mul, norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (stdOrthonormalBasis ℝ E i) x
    rw [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_mul] at hi
    exact mul_le_mul hi
      (mul_le_mul (hA x) (coordinateDerivative_norm_le E hLip i x) (norm_nonneg _) hAn)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  exact gaussian_dirichlet E (hu.differentiable (by norm_num)) hv h0 h1 h2 hX

end GradientHessian.GaussianConcentration
