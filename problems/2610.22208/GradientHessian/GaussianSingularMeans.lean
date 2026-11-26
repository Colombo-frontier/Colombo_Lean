import GradientHessian.GaussianSphereComparison
import GradientHessian.GaussianComparisonProjections
import GradientHessian.GaussianFrobeniusOperator
import GradientHessian.GaussianConcentrationNorm

/-! Exact expected extreme singular values of the independent standard
Gaussian matrix, obtained from the proved sphere comparison and the actual
Gaussian projection laws. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped InnerProductSpace

variable (a b : ℕ) [NeZero a] [NeZero b]

theorem gaussian_matrix_mean_comparison :
    (∫ z, ‖frobeniusOperator a b z‖ ∂euclideanGaussianLaw (FrobeniusSpace a b)) ≤
      (∫ x, ‖x‖ ∂euclideanGaussianLaw (EuclideanSpace ℝ (Fin a))) +
      (∫ x, ‖x‖ ∂euclideanGaussianLaw (EuclideanSpace ℝ (Fin b))) ∧
    (∫ x, ‖x‖ ∂euclideanGaussianLaw (EuclideanSpace ℝ (Fin a))) -
      (∫ x, ‖x‖ ∂euclideanGaussianLaw (EuclideanSpace ℝ (Fin b))) ≤
      ∫ z, leastExpansion (frobeniusOperator a b z) ∂euclideanGaussianLaw (FrobeniusSpace a b) := by
  let T := (frobeniusOperator a b).comp (comparisonMatrix a b)
  have hx (u : EuclideanSpace ℝ (Fin b)) (v : EuclideanSpace ℝ (Fin a))
      (z : MatrixComparisonSpace a b) :
      ⟪matrixComparisonX u v,z⟫_ℝ = ⟪v,T z u⟫_ℝ + comparisonScalar a b z :=
    matrixComparisonX_projection u v z
  have h := gaussian_sphere_mean_comparison T (comparisonRow a b) (comparisonColumn a b)
    (comparisonScalar a b) hx matrixComparisonY_projection (comparisonScalar_mean a b)
  have hT : (∫ z, ‖T z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) =
      ∫ z, ‖frobeniusOperator a b z‖ ∂euclideanGaussianLaw (FrobeniusSpace a b) := by
    rw [← comparisonMatrix_law a b,integral_map_of_stronglyMeasurable
      (comparisonMatrix a b).measurable
      ((frobeniusOperator a b).continuous.norm.stronglyMeasurable)]
    rfl
  have ht : (∫ z, leastExpansion (T z) ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) =
      ∫ z, leastExpansion (frobeniusOperator a b z) ∂euclideanGaussianLaw (FrobeniusSpace a b) := by
    have hf : StronglyMeasurable (fun z => leastExpansion (frobeniusOperator a b z)) :=
      (leastExpansion_lipschitz.continuous.comp (frobeniusOperator a b).continuous).stronglyMeasurable
    rw [← comparisonMatrix_law a b,integral_map_of_stronglyMeasurable
      (comparisonMatrix a b).measurable hf]
    rfl
  have hg : (∫ z, ‖comparisonRow a b z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) =
      ∫ x, ‖x‖ ∂euclideanGaussianLaw (EuclideanSpace ℝ (Fin a)) := by
    rw [← comparisonRow_law a b,integral_map_of_stronglyMeasurable
      (comparisonRow a b).measurable continuous_norm.stronglyMeasurable]
  have hh : (∫ z, ‖comparisonColumn a b z‖ ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) =
      ∫ x, ‖x‖ ∂euclideanGaussianLaw (EuclideanSpace ℝ (Fin b)) := by
    rw [← comparisonColumn_law a b,integral_map_of_stronglyMeasurable
      (comparisonColumn a b).measurable continuous_norm.stronglyMeasurable]
  rwa [hT,ht,hg,hh] at h

theorem gaussian_largestExpansion_mean :
    (∫ z, ‖frobeniusOperator a b z‖ ∂euclideanGaussianLaw (FrobeniusSpace a b)) ≤
      Real.sqrt a + Real.sqrt b := by
  have ha := (mean_norm_bounds (EuclideanSpace ℝ (Fin a))).2
  have hb := (mean_norm_bounds (EuclideanSpace ℝ (Fin b))).2
  simp only [finrank_euclideanSpace_fin] at ha hb
  exact (gaussian_matrix_mean_comparison a b).1.trans (add_le_add ha hb)

theorem gaussian_leastExpansion_mean :
    Real.sqrt ((a : ℝ)-1) - Real.sqrt b ≤
      ∫ z, leastExpansion (frobeniusOperator a b z) ∂euclideanGaussianLaw (FrobeniusSpace a b) := by
  have ha := (mean_norm_bounds (EuclideanSpace ℝ (Fin a))).1
  have hb := (mean_norm_bounds (EuclideanSpace ℝ (Fin b))).2
  simp only [finrank_euclideanSpace_fin] at ha hb
  exact (sub_le_sub ha hb).trans (gaussian_matrix_mean_comparison a b).2

end GradientHessian.GaussianConcentration
