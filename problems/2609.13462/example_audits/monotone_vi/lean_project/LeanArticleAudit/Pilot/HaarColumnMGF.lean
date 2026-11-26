import LeanArticleAudit.Pilot.Stiefel
import LeanArticleAudit.Pilot.SphereRecurrence

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace LeanArticleAudit.Pilot

noncomputable section

variable {d : ℕ}

/-- The orthogonal matrix of a Euclidean linear isometry, in the canonical basis. -/
def orthogonalMatrixOfLinearIsometryEquiv
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    RealOrthogonalGroup d :=
  ⟨U.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    U.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin d) ℝ)
      (EuclideanSpace.basisFun (Fin d) ℝ)⟩

/-- Left multiplication by the matrix of `U` applies `U` to every column. -/
theorem orthogonalColumn_mul_orthogonalMatrixOfLinearIsometryEquiv
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (Q : RealOrthogonalGroup d) (j : Fin d) :
    orthogonalColumn (orthogonalMatrixOfLinearIsometryEquiv U * Q) j =
      U (orthogonalColumn Q j) := by
  apply WithLp.ofLp_injective 2
  change (fun i => ((orthogonalMatrixOfLinearIsometryEquiv U :
      Matrix (Fin d) (Fin d) ℝ) * (Q : Matrix (Fin d) (Fin d) ℝ)) i j) =
    (U (orthogonalColumn Q j)).ofLp
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis U.toLinearMap
    (orthogonalColumn Q j)
  have hrepr : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.repr
      (orthogonalColumn Q j) = fun i => (Q : Matrix (Fin d) (Fin d) ℝ) i j := by
    funext q
    simp [orthogonalColumn, OrthonormalBasis.coe_toBasis_repr_apply]
  rw [hrepr] at h
  funext i
  have hi := congrFun h i
  simpa [orthogonalMatrixOfLinearIsometryEquiv, orthogonalColumn,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi

/-- Every fixed column of a normalized Haar orthogonal matrix is uniform on
the Euclidean unit sphere. -/
theorem orthogonalHaarColumn_isUniform (hd : 1 ≤ d) (j : Fin d) :
    IsUniformUnitSphereLaw d (fun Q : RealOrthogonalGroup d => orthogonalColumn Q j)
      (orthogonalHaarProbability d) := by
  refine ⟨?_, (measurable_orthogonalColumn j).aemeasurable, ?_, ?_⟩
  · simp
  · filter_upwards [] with Q
    exact (orthonormal_orthogonalColumn Q).norm_eq_one j
  · intro U
    let A : RealOrthogonalGroup d := orthogonalMatrixOfLinearIsometryEquiv U
    have hpoint : (fun Q : RealOrthogonalGroup d => U (orthogonalColumn Q j)) =
        fun Q => orthogonalColumn (A * Q) j := by
      funext Q
      exact (orthogonalColumn_mul_orthogonalMatrixOfLinearIsometryEquiv U Q j).symm
    rw [hpoint]
    calc
      Measure.map (fun Q : RealOrthogonalGroup d => orthogonalColumn (A * Q) j)
          (orthogonalHaarProbability d) =
          Measure.map (orthogonalColumn · j)
            (Measure.map (fun Q : RealOrthogonalGroup d => A * Q)
              (orthogonalHaarProbability d)) := by
                symm
                rw [Measure.map_map (measurable_orthogonalColumn j)
                  (measurable_const_mul A)]
                rfl
      _ = Measure.map (orthogonalColumn · j) (orthogonalHaarProbability d) := by
        rw [map_mul_left_eq_self]

/-- The sharp fixed-column projection MGF obtained from the uniform-sphere theorem. -/
theorem orthogonalHaarColumn_hasSubgaussianMGF (hd : 1 ≤ d) (j : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    HasSubgaussianMGF
      (fun Q : RealOrthogonalGroup d => inner ℝ (orthogonalColumn Q j) y)
      ⟨‖y‖ ^ 2 / d,
        div_nonneg (sq_nonneg ‖y‖) (Nat.cast_nonneg d)⟩
      (orthogonalHaarProbability d) := by
  exact uniformSphere_hasSubgaussianMGF hd (orthogonalHaarColumn_isUniform hd j) y

end

end LeanArticleAudit.Pilot
