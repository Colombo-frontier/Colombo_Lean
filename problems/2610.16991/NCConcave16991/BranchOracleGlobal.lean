import NCConcave16991.BranchOraclePipe
import NCConcave16991.GlobalHardSourceErasure

/-! # Literal global first jets from branch replies and released source arrays -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard
open scoped BigOperators InnerProductSpace ContDiff

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

def outerPublic (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) (z : GlobalHard.Joint V) : ℝ :=
  ∑ j, outerStage (u j) (v j) (precedingScore V v j z) (stateProj V j z) (aProj V j z) (bProj V j z)

theorem outerPublic_contDiff (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) :
    ContDiff ℝ ∞ (outerPublic V u v) := by
  apply ContDiff.sum
  intro j _
  exact outerStage_contDiff (u j) (v j) _ _ _ _ (precedingScore_contDiff V v j)
    (stateProj V j).contDiff (aProj V j).contDiff (bProj V j).contDiff

def globalActionData
    (B : ∀ j : Fin M, ∀ t : Fin N, BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
    (i : ι) (z : GlobalHard.Joint V) : ∀ j, PipeActionData (V j) :=
  fun j ↦ pipeActionData (V j) (B j) i (pipeProj V j z)

def renderComponentValue (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) (d r μ : ℝ)
    (z : GlobalHard.Joint V) (a : ∀ j, PipeActionData (V j)) : ℝ :=
  (∑ j, renderPipeValue (ι := ι) (V j) d r μ (pipeProj V j z) (a j)) + outerPublic V u v z

def renderComponentDerivative (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) (d r μ : ℝ)
    (z : GlobalHard.Joint V) (a : ∀ j, PipeActionData (V j)) : GlobalHard.Joint V →L[ℝ] ℝ :=
  (∑ j, (renderPipeDerivative (ι := ι) (V j) d r μ (pipeProj V j z) (a j)).comp (pipeProj V j)) +
    fderiv ℝ (outerPublic V u v) z

def renderComponentGradient (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) (d r μ : ℝ)
    (z : GlobalHard.Joint V) (a : ∀ j, PipeActionData (V j)) : GlobalHard.Joint V :=
  (InnerProductSpace.toDual ℝ (GlobalHard.Joint V)).symm (renderComponentDerivative (ι := ι) V u v d r μ z a)

variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem renderComponentValue_actionData (d r μ : ℝ) (i : ι) (z : GlobalHard.Joint V) :
    renderComponentValue (ι := ι) V u v d r μ z (globalActionData V B i z) = GlobalHard.component V B u v d r μ i z := by
  simp only [renderComponentValue, globalActionData, renderPipeValue_actionData,
    GlobalHard.component, outerPublic, Finset.sum_add_distrib]

theorem component_hasFDerivAt_render (d r μ : ℝ) (i : ι) (z : GlobalHard.Joint V) :
    HasFDerivAt (GlobalHard.component V B u v d r μ i)
      (renderComponentDerivative (ι := ι) V u v d r μ z (globalActionData V B i z)) z := by
  have hp (j : Fin M) : HasFDerivAt
      (fun x : GlobalHard.Joint V ↦ PipeSmoothness.component (B j) d r μ i (pipeProj V j x))
      ((renderPipeDerivative (ι := ι) (V j) d r μ (pipeProj V j z) (globalActionData V B i z j)).comp (pipeProj V j)) z := by
    have hg := PipeSmoothness.component_hasGradientAt (B j) d r μ i (pipeProj V j z)
    have heq := hg.gradient
    rw [← heq, ← renderPipeGradient_actionData] at hg
    have hf := hg.hasFDerivAt
    have ht : (InnerProductSpace.toDual ℝ (PipeSmoothness.Joint (V j)))
        (renderPipeGradient (ι := ι) (V j) d r μ (pipeProj V j z) (pipeActionData (V j) (B j) i (pipeProj V j z))) =
        renderPipeDerivative (ι := ι) (V j) d r μ (pipeProj V j z) (pipeActionData (V j) (B j) i (pipeProj V j z)) :=
      (InnerProductSpace.toDual ℝ (PipeSmoothness.Joint (V j))).apply_symm_apply _
    rw [ht] at hf
    exact hf.comp z (pipeProj V j).hasFDerivAt
  have hs := HasFDerivAt.sum (u := Finset.univ) (fun j _ ↦ hp j)
  have ho := ((outerPublic_contDiff V u v).differentiable (by simp) z).hasFDerivAt
  convert hs.add ho using 1 <;> first
    | rfl
    | (funext x
       simp only [GlobalHard.component, outerPublic, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib])

theorem renderComponentGradient_actionData (d r μ : ℝ) (i : ι) (z : GlobalHard.Joint V) :
    renderComponentGradient (ι := ι) V u v d r μ z (globalActionData V B i z) =
      gradient (GlobalHard.component V B u v d r μ i) z := by
  have hg : HasGradientAt (GlobalHard.component V B u v d r μ i)
      (renderComponentGradient (ι := ι) V u v d r μ z (globalActionData V B i z)) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    simp only [renderComponentGradient, LinearIsometryEquiv.apply_symm_apply]
    exact component_hasFDerivAt_render V B u v d r μ i z
  exact hg.gradient.symm

/-- On the literal inactive-suffix event, the complete true oracle answer is
rendered from public query data, the selected matrix replies, and released
source arrays alone. The renderer does not receive hidden branch maps. -/
theorem inactive_firstJet_rendered (r : ℕ) (d q μ : ℝ) (i : ι) (z : GlobalHard.Joint V)
    (hflat : ∀ j : Fin M, r ≤ j.val → stateScore (v j) (stateProj V j z) < deltaGate) :
    (GlobalHard.component V B u v d q μ i z, gradient (GlobalHard.component V B u v d q μ i) z) =
      (renderComponentValue (ι := ι) V (knownIncoming V r u) (knownTerminal V r v) d q μ z (globalActionData V B i z),
       renderComponentGradient (ι := ι) V (knownIncoming V r u) (knownTerminal V r v) d q μ z (globalActionData V B i z)) := by
  rw [renderComponentValue_actionData, renderComponentGradient_actionData]
  exact component_prefix_firstJet V B u v r d q μ i z hflat

end
end NCConcave16991.BranchOracle
