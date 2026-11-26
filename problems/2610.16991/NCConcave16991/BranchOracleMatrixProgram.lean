import NCConcave16991.BranchOracleReply

/-! # One selected-index simultaneous matrix round as a genuine mixed program -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

private theorem actionData_ext {N : ℕ} {V : Fin (N + 1) → Type*} (a b : PipeActionData V)
    (hf : a.forward = b.forward) (ht : a.transpose = b.transpose) : a = b := by
  cases a
  cases b
  simp_all

def matrixRequestCount : ℕ := (M * (m + 1)) * 2

def matrixRequestIndex (j : Fin M) (k : Fin (m + 1)) (side : Fin 2) : Fin (matrixRequestCount M m) :=
  finProdFinEquiv (finProdFinEquiv (j, k), side)

def matrixQueries (a : ι × InverseMarks (ι := ι) E M m) (b : Fin (matrixRequestCount M m)) : MixedRequest (ι := ι) E M m :=
  let p := (finProdFinEquiv (m := M * (m + 1)) (n := 2)).symm b
  let e := (finProdFinEquiv (m := M) (n := m + 1)).symm p.1
  if p.2.val = 0 then forwardMatrixRequest E M m a.2 a.1 e.1 e.2
  else transposeMatrixRequest E M m a.2 a.1 e.1 e.2

theorem matrixQueries_measurable (b : Fin (matrixRequestCount M m)) : Measurable (fun a ↦ matrixQueries (ι := ι) E M m a b) := by
  apply measurable_from_prod_countable_right
  intro i
  dsimp only [matrixQueries]
  split_ifs
  · exact forwardMatrixRequest_measurable E M m i _ _
  · exact transposeMatrixRequest_measurable E M m i _ _

def decodeMatrixReplies (replies : Fin (matrixRequestCount M m) → MixedReply (ι := ι) E M m) :
    GlobalActionCoordinates (MacroSpaces (ι := ι) E M m) := fun j ↦
  ((fun k ↦ replies (matrixRequestIndex M m j k 0) (depthVertex M m j k.succ)),
   (fun k ↦ replies (matrixRequestIndex M m j k 1) (depthVertex M m j k.castSucc)))

theorem decodeMatrixReplies_measurable : Measurable (decodeMatrixReplies (ι := ι) E M m) := by
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun k ↦ (measurable_pi_apply (depthVertex M m j k.succ)).comp
      (measurable_pi_apply (matrixRequestIndex M m j k 0)))
  · exact measurable_pi_iff.mpr (fun k ↦ (measurable_pi_apply (depthVertex M m j k.castSucc)).comp
      (measurable_pi_apply (matrixRequestIndex M m j k 1)))

def matrixProgram :
    OracleProgram.Fixed (MixedRequest (ι := ι) E M m) (MixedReply (ι := ι) E M m)
      (GlobalActionCoordinates (MacroSpaces (ι := ι) E M m)) (ι × InverseMarks (ι := ι) E M m) (matrixRequestCount M m) :=
  OracleProgram.map (OracleProgram.fullPass (matrixQueries E M m) (matrixQueries_measurable E M m))
    (decodeMatrixReplies E M m) (decodeMatrixReplies_measurable E M m)

theorem eval_matrixProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (i : ι) (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m)) :
    coordinateArray (MacroSpaces (ι := ι) E M m)
      (OracleProgram.eval (matrixProgram E M m) (replyOracle E M m Q) (i, queryInverseMarks E M m Q z)) =
      globalActionData (MacroSpaces (ι := ι) E M m) (macroBranches E Q) i z := by
  rw [matrixProgram, OracleProgram.eval_map, OracleProgram.eval_fullPass]
  funext j
  apply actionData_ext
  · funext k
    change replyOracle E M m Q
      (matrixQueries E M m (i, queryInverseMarks E M m Q z) (matrixRequestIndex M m j k 0))
        (depthVertex M m j k.succ) = _
    simp only [matrixQueries, matrixRequestIndex, Equiv.symm_apply_apply, Fin.val_zero, ite_true]
    convert (replyOracle_at_request E M m Q
      (forwardMatrixRequest E M m (queryInverseMarks E M m Q z) i j k)).trans
        (forwardMatrixRequest_answer E M m Q i z j k) using 1 <;> rfl
  · funext k
    change replyOracle E M m Q
      (matrixQueries E M m (i, queryInverseMarks E M m Q z) (matrixRequestIndex M m j k 1))
        (depthVertex M m j k.castSucc) = _
    simp only [matrixQueries, matrixRequestIndex, Equiv.symm_apply_apply, Fin.val_one, one_ne_zero, ite_false]
    convert (replyOracle_at_request E M m Q
      (transposeMatrixRequest E M m (queryInverseMarks E M m Q z) i j k)).trans
        (transposeMatrixRequest_answer E M m Q i z j k) using 1 <;> rfl

end
end NCConcave16991.BranchOracle
