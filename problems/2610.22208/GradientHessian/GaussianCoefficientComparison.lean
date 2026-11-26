import GradientHessian.GaussianSlepian

/-! Coordinate covariance for Gaussian arrays given by actual Hilbert
coefficient vectors. This identifies covariance with their Gram matrix. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped BigOperators InnerProductSpace NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

def gaussianArrayMap (c : I → E) : E →L[ℝ] (I → ℝ) :=
  ContinuousLinearMap.pi (fun i => innerSL ℝ (c i))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Fintype I] in
@[simp] theorem gaussianArrayMap_apply (c : I → E) (z : E) (i : I) :
    gaussianArrayMap E c z i = ⟪c i, z⟫_ℝ := rfl

omit [MeasurableSpace E] [BorelSpace E] [Fintype I] in
theorem gaussianArrayMap_covariance (c d : I → E) (i j : I) :
    coordinateCovariance E (gaussianArrayMap E c) (gaussianArrayMap E d) i j = ⟪c i, d j⟫_ℝ := by
  unfold coordinateCovariance
  simp only [gaussianArrayMap_apply]
  conv_lhs => arg 2; ext k; rw [real_inner_comm (stdOrthonormalBasis ℝ E k) (d j)]
  exact (stdOrthonormalBasis ℝ E).sum_inner_mul_inner (c i) (d j)

theorem gaussian_maximum_coefficient_comparison [Nonempty I] [DecidableEq I]
    (c d : I → E) (hcross : ∀ i j, ⟪c i, d j⟫_ℝ = 0)
    (hdiag : ∀ i, ‖c i‖ = ‖d i‖) (hcov : ∀ i j, ⟪d i, d j⟫_ℝ ≤ ⟪c i, c j⟫_ℝ) :
    (∫ z, finiteMaximum (fun i => ⟪c i,z⟫_ℝ) ∂euclideanGaussianLaw E) ≤
      ∫ z, finiteMaximum (fun i => ⟪d i,z⟫_ℝ) ∂euclideanGaussianLaw E := by
  apply gaussian_finiteMaximum_comparison E (gaussianArrayMap E c) (gaussianArrayMap E d)
  · intro i j
    rw [gaussianArrayMap_covariance]
    exact hcross i j
  · intro i
    rw [gaussianArrayMap_covariance, gaussianArrayMap_covariance,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hdiag]
  · intro i j
    rw [gaussianArrayMap_covariance, gaussianArrayMap_covariance]
    exact hcov i j

end GradientHessian.GaussianConcentration
