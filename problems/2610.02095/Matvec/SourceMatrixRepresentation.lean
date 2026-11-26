import Matvec.SourceMatrixGeometry
import Matvec.MeasurableSimulation

/-! Every continuous operator on a finite Euclidean coordinate space has an
explicit matrix. Operator symmetry and the actual source-solving guarantee
transfer to that matrix without any change of queries or seed law. -/
namespace Matvec
open Matrix MeasureTheory MeasurableSimulation
open scoped Matrix
noncomputable section

def explicitMatrix {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι) : Matrix ι κ ℝ :=
  Matrix.toEuclideanLin.symm H.toLinearMap

theorem toEuclideanLin_explicitMatrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin (explicitMatrix H) = H.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply H.toLinearMap

theorem euclideanMatrixMap_explicitMatrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι) :
    euclideanMatrixMap (explicitMatrix H) = H := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (explicitMatrix H) x = H x
  rw [toEuclideanLin_explicitMatrix]
  rfl

theorem explicitMatrix_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hH : H.toLinearMap.IsSymmetric) : (explicitMatrix H)ᵀ = explicitMatrix H := by
  have h : (explicitMatrix H).IsHermitian := Matrix.isHermitian_iff_isSymmetric.mpr
    (by rw [toEuclideanLin_explicitMatrix]; exact hH)
  change (explicitMatrix H).conjTranspose = explicitMatrix H at h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem source_policy_success_of_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Seed : Type*} [MeasurableSpace Seed] {K : ℕ}
    (base : Policy (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) K
      (EuclideanSpace ℝ ι × Seed)) (μ : Measure Seed) (L : ℝ)
    (hsuccess : ∀ A : Matrix ι ι ℝ, Aᵀ = A →
      (∀ w, ‖w‖ ≤ ‖Matrix.toEuclideanLin A w‖) → ‖euclideanMatrixMap A‖ ≤ L →
      ∀ r, 3 / 5 ≤ μ.real
        {s | ‖euclideanMatrixMap A (base.run (euclideanMatrixMap A) (r, s)) - r‖ ≤ ‖r‖ / 2}) :
    ∀ H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι,
      H.toLinearMap.IsSymmetric → (∀ w, ‖w‖ ≤ ‖H w‖) → ‖H‖ ≤ L →
      ∀ r, 3 / 5 ≤ μ.real {s | ‖H (base.run H (r, s)) - r‖ ≤ ‖r‖ / 2} := by
  intro H hsym hexp hnorm r
  have h := hsuccess (explicitMatrix H) (explicitMatrix_symmetric H hsym)
    (by simpa only [toEuclideanLin_explicitMatrix] using hexp)
    (by simpa only [euclideanMatrixMap_explicitMatrix] using hnorm) r
  simpa only [euclideanMatrixMap_explicitMatrix] using h

end
end Matvec
