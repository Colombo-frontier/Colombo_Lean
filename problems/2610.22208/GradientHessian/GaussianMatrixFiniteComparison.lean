import GradientHessian.GaussianGordon
import GradientHessian.GaussianCoefficientComparison
import GradientHessian.GaussianMatrixComparisonCoefficients

/-! The manuscript's two finite-array comparisons, for the actual
matrix-plus-scalar and independent-vector coefficient processes. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped BigOperators InnerProductSpace

variable {a b : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

theorem matrix_finiteMaximum_comparison
    (u : I → EuclideanSpace ℝ (Fin b)) (v : J → EuclideanSpace ℝ (Fin a))
    (hu : ∀ i, ‖u i‖=1) (hv : ∀ j, ‖v j‖=1) :
    (∫ z : MatrixComparisonSpace a b,
      finiteMaximum (fun p : I × J => ⟪matrixComparisonX (u p.1) (v p.2),z⟫_ℝ)
        ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤
    ∫ z : MatrixComparisonSpace a b,
      finiteMaximum (fun p : I × J => ⟪matrixComparisonY (u p.1) (v p.2),z⟫_ℝ)
        ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
  apply gaussian_finiteMaximum_comparison (MatrixComparisonSpace a b)
    (gaussianArrayMap _ (fun p : I × J => matrixComparisonX (u p.1) (v p.2)))
    (gaussianArrayMap _ (fun p : I × J => matrixComparisonY (u p.1) (v p.2)))
  · intro p q
    rw [gaussianArrayMap_covariance]
    exact matrixComparison_cross _ _ _ _
  · intro p
    rw [gaussianArrayMap_covariance, gaussianArrayMap_covariance]
    exact matrixComparison_same_row _ _ _ (hu p.1)
  · intro p q
    rw [gaussianArrayMap_covariance, gaussianArrayMap_covariance]
    exact matrixComparison_covariance_order _ _ _ _ (hu p.1) (hu q.1) (hv p.2) (hv q.2)

theorem matrix_finiteMinMax_comparison
    (u : I → EuclideanSpace ℝ (Fin b)) (v : J → EuclideanSpace ℝ (Fin a))
    (hu : ∀ i, ‖u i‖=1) (hv : ∀ j, ‖v j‖=1) :
    (∫ z : MatrixComparisonSpace a b,
      finiteMinMax (fun p : I × J => ⟪matrixComparisonY (u p.1) (v p.2),z⟫_ℝ)
        ∂euclideanGaussianLaw (MatrixComparisonSpace a b)) ≤
    ∫ z : MatrixComparisonSpace a b,
      finiteMinMax (fun p : I × J => ⟪matrixComparisonX (u p.1) (v p.2),z⟫_ℝ)
        ∂euclideanGaussianLaw (MatrixComparisonSpace a b) := by
  apply gaussian_finiteMinMax_comparison (MatrixComparisonSpace a b)
    (gaussianArrayMap _ (fun p : I × J => matrixComparisonX (u p.1) (v p.2)))
    (gaussianArrayMap _ (fun p : I × J => matrixComparisonY (u p.1) (v p.2)))
  · intro p q
    rw [gaussianArrayMap_covariance]
    exact matrixComparison_cross _ _ _ _
  · intro i j l
    rw [gaussianArrayMap_covariance, gaussianArrayMap_covariance]
    exact matrixComparison_same_row _ _ _ (hu i)
  · intro p q
    rw [gaussianArrayMap_covariance, gaussianArrayMap_covariance]
    exact matrixComparison_covariance_order _ _ _ _ (hu p.1) (hu q.1) (hv p.2) (hv q.2)

end GradientHessian.GaussianConcentration
