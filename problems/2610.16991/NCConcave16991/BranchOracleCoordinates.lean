import NCConcave16991.BranchOracleGlobal
import NCConcave16991.GlobalHardEuclidean

/-! # Exact gradient transport for the Euclidean first-jet renderer -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHardEuclidean
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

theorem hasGradientAt_comp_isometry_symm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} {g x : E} (hg : HasGradientAt f g x) :
    HasGradientAt (fun y ↦ f (Q.symm y)) (Q g) (Q x) := by
  have hf : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) g) (Q.symm (Q x)) := by
    simpa using hg.hasFDerivAt
  have hh := hf.comp (Q x) Q.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hh.congr_fderiv ?_
  ext h
  change ⟪g, Q.symm h⟫_ℝ = ⟪Q g, h⟫_ℝ
  calc
    _ = ⟪Q g, Q (Q.symm h)⟫_ℝ := (Q.inner_map_map _ _).symm
    _ = _ := by rw [Q.apply_symm_apply]

theorem gradient_comp_isometry_symm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : E ≃ₗᵢ[ℝ] F) (f : E → ℝ) (y : F) (hf : DifferentiableAt ℝ f (Q.symm y)) :
    gradient (fun w ↦ f (Q.symm w)) y = Q (gradient f (Q.symm y)) := by
  have hh := hasGradientAt_comp_isometry_symm Q hf.hasGradientAt
  simpa only [Q.apply_symm_apply] using hh.gradient

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem euclidean_component_gradient_rendered (d r μ : ℝ) (i : Fin n)
    (z : JointSpace (primalDimension V) (dualDimension V)) :
    gradient (GlobalHardEuclidean.component V B u v d r μ i) z =
      jointCoordinates V (renderComponentGradient (ι := Fin n) V u v d r μ ((jointCoordinates V).symm z)
        (globalActionData V B i ((jointCoordinates V).symm z))) := by
  rw [renderComponentGradient_actionData]
  exact gradient_comp_isometry_symm (jointCoordinates V) (GlobalHard.component V B u v d r μ i) z
    ((GlobalHard.component_contDiff V B u v d r μ i).differentiable (by simp) _)

end
end NCConcave16991.BranchOracle
