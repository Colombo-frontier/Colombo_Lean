import NCConcave16991.BranchOracleMarkProgram
import NCConcave16991.BranchOracleMatrixProgram
import NCConcave16991.BranchOracleSourceProgram
import NCConcave16991.BranchOracleCachedResponse
import NCConcave16991.BranchOracleInterpreterMeasurable
import NCConcave16991.OracleProgramBind
import NCConcave16991.OracleProgramTransform

/-! # The literal complete component reply compiled into mixed requests

The program first obtains five inverse marks at every vertex, then requests
the selected matrix prepend/slice replies, closes the public release rule,
and exposes only the resulting source prefix.  Its constructor receives no
hidden rotation, branch map, or true component oracle.
-/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {D : ℝ} (K : KnownDualDomain (dualDimension (MacroSpaces (ι := Fin n) E M m)) D)
variable [BorelSpace (GlobalHard.Joint (MacroSpaces (ι := Fin n) E M m))]
  [OpensMeasurableSpace (SourceParameters (MacroSpaces (ι := Fin n) E M m))]
  [OpensMeasurableSpace (GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m))]

abbrev StepInput := Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m) K ×
  OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K

def queryMarksStepProgram : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (InverseMarks (ι := Fin n) E M m) (StepInput E K) (queryMarkCount M m) :=
  OracleProgram.withSeed (queryMarkProgram E M m)
    (fun a : StepInput E K ↦ queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2)
    ((queryGlobal_continuous (MacroSpaces (ι := Fin n) E M m) K).measurable.comp measurable_snd)

def markedMatrixProgram : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m)) (StepInput E K)
    (queryMarkCount M m + matrixRequestCount M m) :=
  OracleProgram.bind (queryMarksStepProgram E K)
    (OracleProgram.withSeed (matrixProgram E M m)
      (fun a : StepInput E K × InverseMarks (ι := Fin n) E M m ↦ (a.1.2.1, a.2))
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))

theorem eval_markedMatrixProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (a : StepInput E K) :
    coordinateArray (MacroSpaces (ι := Fin n) E M m)
      (OracleProgram.eval (markedMatrixProgram E K) (replyOracle E M m Q) a) =
      globalActionData (MacroSpaces (ι := Fin n) E M m) (macroBranches E Q) a.2.1
        (queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2) := by
  rw [markedMatrixProgram, OracleProgram.eval_bind, OracleProgram.eval_withSeed,
    queryMarksStepProgram, OracleProgram.eval_withSeed, eval_queryMarkProgram]
  exact eval_matrixProgram E M m Q a.2.1 _

variable (e : E) (ρ d c μ : ℝ)

def finishFromCaches
    (a : StepInput E K) (actions : GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m))
    (cache : MixedReply (ι := Fin n) E M m) : Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m) K :=
  let after := Reference.roundUpdate (MacroSpaces (ι := Fin n) E M m) K ρ (macroSite (M := M) m) a
  let sources := sourcesFromCache E M m after.1 cache
  ⟨after.2, after.1, OraclePolicy.appendHistory K a.1.history
    (a.2, renderCachedAnswer (MacroSpaces (ι := Fin n) E M m) K d c μ ((sources, a.2), actions))⟩

theorem finishFromCaches_measurable : Measurable
    (fun a : (StepInput E K × GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m)) × MixedReply (ι := Fin n) E M m ↦
      finishFromCaches E K ρ d c μ a.1.1 a.1.2 a.2) := by
  let X := (StepInput E K × GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m)) × MixedReply (ι := Fin n) E M m
  let after : X → ℕ × WordProfile (Fin n) := fun a ↦
    Reference.roundUpdate (MacroSpaces (ι := Fin n) E M m) K ρ (macroSite (M := M) m) a.1.1
  have ha : Measurable after := (Reference.roundUpdate_measurable (n := n) (MacroSpaces (ι := Fin n) E M m) K ρ
    (macroSite (M := M) m)).comp (measurable_fst.comp measurable_fst)
  let sources : X → SourceParameters (MacroSpaces (ι := Fin n) E M m) :=
    fun a ↦ sourcesFromCache E M m (after a).1 a.2
  have hs : Measurable sources := (sourcesFromCache_measurable E M m).comp (ha.fst.prodMk measurable_snd)
  let input : X → CachedReplyInput (n := n) (MacroSpaces (ι := Fin n) E M m) K :=
    fun a ↦ ((sources a, a.1.1.2), a.1.2)
  have hi : Measurable input := (hs.prodMk (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
    (measurable_snd.comp measurable_fst)
  have hr : Measurable (fun a : X ↦ renderCachedAnswer (MacroSpaces (ι := Fin n) E M m) K d c μ (input a)) :=
    (renderCachedAnswer_measurable (MacroSpaces (ι := Fin n) E M m) K d c μ).comp hi
  let hist : X → OraclePolicy.History K (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) :=
    fun a ↦ OraclePolicy.appendHistory K a.1.1.1.history
      (a.1.1.2, renderCachedAnswer (MacroSpaces (ι := Fin n) E M m) K d c μ (input a))
  have hh : Measurable hist := (OraclePolicy.appendHistory_measurable K).comp
    (((Reference.history_measurable (MacroSpaces (ι := Fin n) E M m) K).comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk hr))
  convert Reference.state_mk_measurable (MacroSpaces (ι := Fin n) E M m) K
    (fun a : X ↦ (after a).2) (fun a : X ↦ (after a).1) hist ha.snd ha.fst hh using 1
  funext a
  rfl

def sourceFinishProgram : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (StepInput E K × GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m)) (M * (m + 1) + 1) :=
  OracleProgram.mapWithSeed
    (OracleProgram.withSeed (sourceProgram E M m)
      (fun a : StepInput E K × GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m) ↦
        ((Reference.roundUpdate (MacroSpaces (ι := Fin n) E M m) K ρ (macroSite (M := M) m) a.1).1, e))
      (((Reference.roundUpdate_measurable (n := n) (MacroSpaces (ι := Fin n) E M m) K ρ
        (macroSite (M := M) m)).fst.comp measurable_fst).prodMk measurable_const))
    (fun a cache ↦ finishFromCaches E K ρ d c μ a.1 a.2 cache)
    (finishFromCaches_measurable E K ρ d c μ)

def componentMixedCost : ℕ := queryMarkCount M m + matrixRequestCount M m + (M * (m + 1) + 1)

def componentStepProgram : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m) K) (StepInput E K) (componentMixedCost (M := M) (m := m)) :=
  OracleProgram.bind (markedMatrixProgram E K) (sourceFinishProgram E K e ρ d c μ)

theorem eval_componentStepProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (a : StepInput E K) :
    OracleProgram.eval (componentStepProgram E K e ρ d c μ) (replyOracle E M m Q) a =
      Reference.step (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ a.1 a.2 := by
  rw [componentStepProgram, OracleProgram.eval_bind, sourceFinishProgram,
    OracleProgram.eval_mapWithSeed, OracleProgram.eval_withSeed]
  dsimp only [finishFromCaches]
  rw [sourcesFromCache_eval_sourceProgram]
  have hh := eval_markedMatrixProgram E K Q a
  dsimp only [renderCachedAnswer]
  rw [hh]
  rfl

end
end NCConcave16991.BranchOracle
