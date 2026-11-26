import NCConcave16991.PipeSmoothness

/-! # Exact selected-pipe first jets from one forward and transpose action -/

namespace NCConcave16991.BranchOracle
noncomputable section
open scoped BigOperators InnerProductSpace
open BranchGeometry PipeSmoothness

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {N : ℕ} (V : Fin (N + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)] [∀ j, CompleteSpace (V j)]

structure PipeActionData where
  forward : ∀ t : Fin N, V t.succ
  transpose : ∀ t : Fin N, V t.castSucc

def pipeActionData (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (i : ι) (z : PipeSmoothness.Joint V) : PipeActionData V where
  forward t := (B t).branch i (wProj t.castSucc z)
  transpose t := ((B t).branch i).toContinuousLinearMap.adjoint (wProj t.succ z)

/-- All terms not using the hidden selected branch action are public. -/
def pipePublicBilinear (d r μ : ℝ) : PipeSmoothness.Joint V →L[ℝ] PipeSmoothness.Joint V →L[ℝ] ℝ :=
  d • (innerPair aProj aProj + innerPair bProj bProj) +
  r • (innerPair aProj (wProj 0) - innerPair bProj (wProj (Fin.last N))) -
  (beta ι / 2) • (μ • (∑ j, innerPair (wProj j) (wProj j)) +
    ∑ t : Fin N, (innerPair (wProj t.castSucc) (wProj t.castSucc) + innerPair (wProj t.succ) (wProj t.succ)))

def renderPipeValue (d r μ : ℝ) (z : PipeSmoothness.Joint V) (a : PipeActionData V) : ℝ :=
  pipePublicBilinear (ι := ι) V d r μ z z + ∑ t, ⟪wProj t.succ z, a.forward t⟫_ℝ

def renderPipeDerivative (d r μ : ℝ) (z : PipeSmoothness.Joint V) (a : PipeActionData V) :
    PipeSmoothness.Joint V →L[ℝ] ℝ :=
  pipePublicBilinear (ι := ι) V d r μ z + (pipePublicBilinear (ι := ι) V d r μ).flip z +
    ∑ t, ((innerSL ℝ (a.transpose t)).comp (wProj t.castSucc) +
      (innerSL ℝ (a.forward t)).comp (wProj t.succ))

def renderPipeGradient (d r μ : ℝ) (z : PipeSmoothness.Joint V) (a : PipeActionData V) : PipeSmoothness.Joint V :=
  (InnerProductSpace.toDual ℝ (PipeSmoothness.Joint V)).symm (renderPipeDerivative (ι := ι) V d r μ z a)

theorem renderPipeValue_actionData (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) (z : PipeSmoothness.Joint V) :
    renderPipeValue (ι := ι) V d r μ z (pipeActionData V B i z) = PipeSmoothness.component B d r μ i z := by
  unfold PipeSmoothness.component
  rw [← componentBilinear_diagonal]
  simp only [renderPipeValue, pipePublicBilinear, pipeActionData, componentBilinear,
    add_apply, sub_apply, smul_apply, sum_apply, innerPair_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    LinearIsometry.coe_toContinuousLinearMap]

theorem renderPipeDerivative_actionData (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) (z : PipeSmoothness.Joint V) :
    renderPipeDerivative (ι := ι) V d r μ z (pipeActionData V B i z) =
      componentBilinear B d r μ i z + (componentBilinear B d r μ i).flip z := by
  have hsplit : componentBilinear B d r μ i = pipePublicBilinear (ι := ι) V d r μ +
      ∑ t : Fin N, innerPair (wProj t.succ) (((B t).branch i).toContinuousLinearMap.comp (wProj t.castSucc)) := rfl
  ext h
  rw [hsplit]
  simp only [renderPipeDerivative, add_apply, sum_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, innerPair_apply, innerSL_apply_apply, pipeActionData]
  simp_rw [ContinuousLinearMap.adjoint_inner_left]
  change pipePublicBilinear (ι := ι) V d r μ z h + pipePublicBilinear (ι := ι) V d r μ h z +
      (∑ t : Fin N, (⟪wProj t.succ z, (B t).branch i (wProj t.castSucc h)⟫_ℝ +
        ⟪(B t).branch i (wProj t.castSucc z), wProj t.succ h⟫_ℝ)) =
      pipePublicBilinear (ι := ι) V d r μ z h +
        (∑ t : Fin N, ⟪wProj t.succ z, (B t).branch i (wProj t.castSucc h)⟫_ℝ) +
        (pipePublicBilinear (ι := ι) V d r μ h z +
          ∑ t : Fin N, ⟪wProj t.succ h, (B t).branch i (wProj t.castSucc z)⟫_ℝ)
  have hc : (∑ t : Fin N, (⟪wProj t.succ z, (B t).branch i (wProj t.castSucc h)⟫_ℝ +
      ⟪(B t).branch i (wProj t.castSucc z), wProj t.succ h⟫_ℝ)) =
      (∑ t : Fin N, ⟪wProj t.succ z, (B t).branch i (wProj t.castSucc h)⟫_ℝ) +
        ∑ t : Fin N, ⟪wProj t.succ h, (B t).branch i (wProj t.castSucc z)⟫_ℝ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [real_inner_comm ((B t).branch i (wProj t.castSucc z)) (wProj t.succ h)]
  rw [hc]
  ring

/-- The full actual pipe gradient uses precisely the returned matrix actions. -/
theorem renderPipeGradient_actionData (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (i : ι) (z : PipeSmoothness.Joint V) :
    renderPipeGradient (ι := ι) V d r μ z (pipeActionData V B i z) = gradient (PipeSmoothness.component B d r μ i) z := by
  rw [(component_hasGradientAt B d r μ i z).gradient]
  apply (InnerProductSpace.toDual ℝ (PipeSmoothness.Joint V)).injective
  simp only [renderPipeGradient, LinearIsometryEquiv.apply_symm_apply]
  ext h
  rw [InnerProductSpace.toDual_apply_apply, quadraticHessian_inner]
  exact congrArg (fun D : PipeSmoothness.Joint V →L[ℝ] ℝ ↦ D h) (renderPipeDerivative_actionData V B d r μ i z)

end
end NCConcave16991.BranchOracle
