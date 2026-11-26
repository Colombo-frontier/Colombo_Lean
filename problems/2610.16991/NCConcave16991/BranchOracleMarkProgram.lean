import NCConcave16991.BranchOracleReply

/-! # Actual finite mixed programs for query and terminal inverse marks -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)
variable [OpensMeasurableSpace (GlobalHard.Joint (MacroSpaces (ι := ι) E M m))]

def queryMarkCount : ℕ := (M * (m + 1) + 1) * 5

def decodeQueryMarks (replies : Fin (queryMarkCount M m) → MixedReply (ι := ι) E M m) :
    InverseMarks (ι := ι) E M m := fun t slot ↦ replies (finProdFinEquiv (t, slot)) t

theorem decodeQueryMarks_measurable : Measurable (decodeQueryMarks (ι := ι) E M m) := by
  apply measurable_pi_iff.mpr
  intro t
  apply measurable_pi_iff.mpr
  intro slot
  exact (measurable_pi_apply t).comp (measurable_pi_apply (finProdFinEquiv (t, slot)))

def queryMarkProgram :
    OracleProgram.Fixed (MixedRequest (ι := ι) E M m) (MixedReply (ι := ι) E M m)
      (InverseMarks (ι := ι) E M m) (GlobalHard.Joint (MacroSpaces (ι := ι) E M m)) (queryMarkCount M m) :=
  OracleProgram.map
    (OracleProgram.fullPass (fun z a ↦ queryRequest E M m z
      ((finProdFinEquiv (m := M * (m + 1) + 1) (n := 5)).symm a).1
      ((finProdFinEquiv (m := M * (m + 1) + 1) (n := 5)).symm a).2)
      (fun a ↦ queryRequest_measurable E M m _ _))
    (decodeQueryMarks E M m) (decodeQueryMarks_measurable E M m)

theorem eval_queryMarkProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m)) :
    OracleProgram.eval (queryMarkProgram E M m) (replyOracle E M m Q) z = queryInverseMarks E M m Q z := by
  rw [queryMarkProgram, OracleProgram.eval_map, OracleProgram.eval_fullPass]
  funext t slot
  simp only [decodeQueryMarks, Equiv.symm_apply_apply]
  exact replyOracle_at_request E M m Q (queryRequest E M m z t slot)

def decodeOutputMarks (replies : Vertex M m → MixedReply (ι := ι) E M m) : MixedReply (ι := ι) E M m :=
  fun t ↦ replies t t

theorem decodeOutputMarks_measurable : Measurable (decodeOutputMarks (ι := ι) E M m) :=
  measurable_pi_iff.mpr (fun t ↦ (measurable_pi_apply t).comp (measurable_pi_apply t))

def outputMarkProgram :
    OracleProgram.Fixed (MixedRequest (ι := ι) E M m) (MixedReply (ι := ι) E M m)
      (MixedReply (ι := ι) E M m) (PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m))) (M * (m + 1) + 1) :=
  OracleProgram.map (OracleProgram.fullPass (fun c t ↦ outputRequest E M m c t)
      (fun t ↦ outputRequest_measurable E M m t))
    (decodeOutputMarks E M m) (decodeOutputMarks_measurable E M m)

theorem eval_outputMarkProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m))) :
    OracleProgram.eval (outputMarkProgram E M m) (replyOracle E M m Q) c =
      (fun t : Vertex M m ↦ (Q t.val).symm (outputMark E M m t.val c)) := by
  rw [outputMarkProgram, OracleProgram.eval_map, OracleProgram.eval_fullPass]
  funext t
  exact replyOracle_at_request E M m Q (outputRequest E M m c t)

end
end NCConcave16991.BranchOracle
