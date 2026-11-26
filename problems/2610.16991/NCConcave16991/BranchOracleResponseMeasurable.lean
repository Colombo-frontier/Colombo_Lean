import NCConcave16991.BranchOracleResponse
import NCConcave16991.BranchOracleMeasurable

/-! # Measurable Euclidean reference replies with an adaptive source prefix -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))

def actionCoordinates (i : Fin n) (z : GlobalHard.Joint V) : GlobalActionCoordinates V := fun j ↦
  ((fun t ↦ (B j t).branch i (PipeSmoothness.wProj t.castSucc (pipeProj V j z))),
   (fun t ↦ ((B j t).branch i).toContinuousLinearMap.adjoint (PipeSmoothness.wProj t.succ (pipeProj V j z))))

theorem actionCoordinates_continuous (i : Fin n) : Continuous (actionCoordinates V B i) := by
  apply continuous_pi
  intro j
  apply Continuous.prodMk
  · apply continuous_pi
    intro t
    exact ((B j t).branch i).continuous.comp ((PipeSmoothness.wProj t.castSucc).continuous.comp (pipeProj V j).continuous)
  · apply continuous_pi
    intro t
    exact ((B j t).branch i).toContinuousLinearMap.adjoint.continuous.comp
      ((PipeSmoothness.wProj t.succ).continuous.comp (pipeProj V j).continuous)

theorem coordinateArray_actionCoordinates (i : Fin n) (z : GlobalHard.Joint V) :
    coordinateArray V (actionCoordinates V B i z) = globalActionData V B i z := by
  funext j
  rfl

variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))

theorem referenceResponse_fixed_measurable (r : ℕ) (d c μ : ℝ) :
    Measurable (referenceResponse V K B u v r d c μ) := by
  letI (j : Fin M) (k : Fin (N + 1)) : MeasurableSpace (V j k) := borel (V j k)
  letI (j : Fin M) (k : Fin (N + 1)) : BorelSpace (V j k) := ⟨rfl⟩
  apply measurable_from_prod_countable_right
  intro i
  let z : PrimalSpace (primalDimension V) × K.carrier → GlobalHard.Joint V :=
    fun a ↦ (jointCoordinates V).symm (jointPoint a.1 a.2.val)
  have hz : Continuous z := (jointCoordinates V).symm.continuous.comp
    ((WithLp.prod_continuous_toLp 2 _ _).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let input : PrimalSpace (primalDimension V) × K.carrier → RendererInput V := fun a ↦
    (((knownIncoming V r u, knownTerminal V r v), z a), actionCoordinates V B i (z a))
  have hi : Continuous input := (continuous_const.prodMk hz).prodMk ((actionCoordinates_continuous V B i).comp hz)
  have hj := (renderEncodedFirstJet_measurable (ι := Fin n) V d c μ).comp hi.measurable
  let post : ℝ × GlobalHard.Joint V → OracleAnswer (primalDimension V) (dualDimension V) :=
    fun a ↦ (a.1, ((jointCoordinates V a.2).fst, (jointCoordinates V a.2).snd))
  have hg : Continuous (fun a : ℝ × GlobalHard.Joint V ↦ jointCoordinates V a.2) :=
    (jointCoordinates V).continuous.comp continuous_snd
  have hp : Continuous post := continuous_fst.prodMk
    (((WithLp.fstL 2 ℝ _ _).continuous.comp hg).prodMk ((WithLp.sndL 2 ℝ _ _).continuous.comp hg))
  convert hp.measurable.comp hj using 1
  funext a
  simp only [Function.comp_apply, post, input, renderEncodedValue, renderEncodedGradient,
    referenceResponse, renderOracleAnswer, queryGlobal, z, queryPoint, coordinateArray_actionCoordinates]

theorem referenceResponse_measurable (d c μ : ℝ) :
    Measurable (fun a : ℕ × OracleQuery n (primalDimension V) K ↦ referenceResponse V K B u v a.1 d c μ a.2) := by
  apply measurable_from_prod_countable_right
  intro r
  exact referenceResponse_fixed_measurable V B K u v r d c μ

end
end NCConcave16991.BranchOracle
