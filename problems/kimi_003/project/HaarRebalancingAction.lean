import HaarRebalancing

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace Task006.HaarRebalancing
noncomputable section
variable {d : ℕ}

/-- The actual isometric action of an orthogonal matrix on Euclidean space. -/
def action (Q : OrthogonalGroup d) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  Unitary.linearIsometryEquiv
    (Unitary.map
      { toFun := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
        map_one' := map_one Matrix.toEuclideanCLM
        map_mul' := map_mul Matrix.toEuclideanCLM
        map_star' := map_star Matrix.toEuclideanCLM } Q)

@[simp] theorem action_apply (Q : OrthogonalGroup d) (x : EuclideanSpace ℝ (Fin d)) :
    action Q x = Matrix.toEuclideanCLM (𝕜 := ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) x := rfl

@[simp] theorem action_mul (Q A : OrthogonalGroup d) (x : EuclideanSpace ℝ (Fin d)) :
    action (Q * A) x = action Q (action A x) := by
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) ((Q : Matrix (Fin d) (Fin d) ℝ) *
    (A : Matrix (Fin d) (Fin d) ℝ))) x = _
  rw [map_mul]
  rfl

theorem action_joint_continuous :
    Continuous (fun p : OrthogonalGroup d × EuclideanSpace ℝ (Fin d) => action p.1 p.2) := by
  change Continuous (fun p : OrthogonalGroup d × EuclideanSpace ℝ (Fin d) =>
    WithLp.toLp 2 (fun i => ∑ j, ((p.1 : Matrix (Fin d) (Fin d) ℝ) i j) * (p.2 j)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j hj
  apply Continuous.mul
  · have hcoord : Continuous
        (fun Q : Matrix (Fin d) (Fin d) ℝ => Q i j) :=
        (continuous_apply j).comp (continuous_apply i)
    exact hcoord.comp (continuous_subtype_val.comp continuous_fst)
  · exact (EuclideanSpace.proj j).continuous.comp continuous_snd

/-- The matrix of an ambient isometry acts by that exact isometry. -/
theorem action_matrixOfIsometry
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    action (orthogonalMatrixOfLinearIsometryEquiv U) x = U x := by
  apply WithLp.ofLp_injective 2
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis U.toLinearMap x
  have hrepr : ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.repr x : Fin d → ℝ) = x.ofLp := by
    funext i
    simp
  change _ *ᵥ _ = _ at h
  rw [hrepr] at h
  funext i
  have hi := congrFun h i
  simpa [action_apply, orthogonalMatrixOfLinearIsometryEquiv,
    Matrix.ofLp_toEuclideanCLM, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using hi

/-- Equal-radius vectors are related by an actual orthogonal action, via a
reflection in their difference. No measurable choice of rotations is assumed. -/
theorem action_transitive_on_sphere (x y : EuclideanSpace ℝ (Fin d))
    (hxy : ‖x‖ = ‖y‖) : ∃ Q : OrthogonalGroup d, action Q x = y := by
  let U := (ℝ ∙ (x - y))ᗮ.reflection
  refine ⟨orthogonalMatrixOfLinearIsometryEquiv U, ?_⟩
  rw [action_matrixOfIsometry]
  exact Submodule.reflection_sub hxy

end
end Task006.HaarRebalancing
