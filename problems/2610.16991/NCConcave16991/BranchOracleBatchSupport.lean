import NCConcave16991.BranchOracleEngine
import NCConcave16991.BranchOracleMarkProgram
import NCConcave16991.BranchOracleMatrixProgram
import NCConcave16991.OracleProgramStateLibrary

/-! # Chronological support contracts for the actual mixed program batches -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ) [BorelSpace (GlobalHard.Joint (MacroSpaces (ι := ι) E M m))]
variable {S : Type*} (A : WordEngine (ι := ι) E M m S)
  (p : WordProfile ι) (W : Submodule ℝ E) (hW : A.Covered W)

include hW

theorem evalState_queryMarkProgram_supported (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m))
    (s : S) (hvalid : A.admissible s) (hs : LedgerSupported E M m p W (A.ledger s)) :
    LedgerSupported E M m p W (A.ledger (OracleProgram.evalState (queryMarkProgram E M m) A.oracle z s).2) ∧
      InverseMarksSupported E M m p W (OracleProgram.evalState (queryMarkProgram E M m) A.oracle z s).1 := by
  let qs : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) → Fin (queryMarkCount M m) → MixedRequest (ι := ι) E M m :=
    fun z a ↦ queryRequest E M m z
      ((finProdFinEquiv (m := M * (m + 1) + 1) (n := 5)).symm a).1
      ((finProdFinEquiv (m := M * (m + 1) + 1) (n := 5)).symm a).2
  let hq : ∀ a, Measurable (fun z ↦ qs z a) := fun _ ↦ queryRequest_measurable E M m _ _
  let good : Fin (queryMarkCount M m) → MixedReply (ι := ι) E M m → Prop := fun i r ↦
    let t := ((finProdFinEquiv (m := M * (m + 1) + 1) (n := 5)).symm i).1
    r t ∈ wordSupport t.val (p.words t.val) W
  have hh := OracleProgram.evalState_fullPass_spec qs hq A.oracle z
    (fun s ↦ A.admissible s ∧ LedgerSupported E M m p W (A.ledger s)) good (fun i state hstate ↦ ?_) s ⟨hvalid, hs⟩
  · rw [queryMarkProgram, OracleProgram.evalState_map]
    refine ⟨hh.1.2, ?_⟩
    intro t slot
    have ht := hh.2 (finProdFinEquiv (t, slot))
    change (OracleProgram.evalState (OracleProgram.fullPass qs hq) A.oracle z s).1
      (finProdFinEquiv (t, slot)) t ∈ wordSupport t.val (p.words t.val) W
    have he : good (finProdFinEquiv (t, slot))
        ((OracleProgram.evalState (OracleProgram.fullPass qs hq) A.oracle z s).1 (finProdFinEquiv (t, slot))) =
        ((OracleProgram.evalState (OracleProgram.fullPass qs hq) A.oracle z s).1 (finProdFinEquiv (t, slot)) t ∈
          wordSupport t.val (p.words t.val) W) :=
      congrArg (fun u : Vertex M m ↦
        (OracleProgram.evalState (OracleProgram.fullPass qs hq) A.oracle z s).1 (finProdFinEquiv (t, slot)) u ∈
          wordSupport u.val (p.words u.val) W)
        (congrArg Prod.fst ((finProdFinEquiv (m := M * (m + 1) + 1) (n := 5)).symm_apply_apply (t, slot)))
    exact he.mp ht
  · exact ⟨⟨A.admissible_step state _ hstate.1,
      A.step_supported p W hW state hstate.1 hstate.2 _ (queryRequest_fits E M m p W z _ _)⟩,
      A.inverse_reply_supported p W hW state hstate.1 hstate.2 _ _⟩

theorem evalState_matrixProgram_supported (marks : InverseMarks (ι := ι) E M m)
    (hm : InverseMarksSupported E M m p W marks) (i : ι)
    (s : S) (hvalid : A.admissible s) (hs : LedgerSupported E M m p W (A.ledger s)) :
    LedgerSupported E M m (p.matrixScheduleStep (fun _ ↦ i)) W
      (A.ledger (OracleProgram.evalState (matrixProgram E M m) A.oracle (i, marks) s).2) := by
  let q := p.matrixScheduleStep (fun _ ↦ i)
  have hinit : LedgerSupported E M m q W (A.ledger s) := fun t ↦
    (hs t).trans (wordSupport_mono (p.words_subset_matrixScheduleStep (fun _ ↦ i) t.val) le_rfl)
  have hh := OracleProgram.evalState_fullPass_spec (matrixQueries E M m) (matrixQueries_measurable E M m)
    A.oracle (i, marks) (fun s ↦ A.admissible s ∧ LedgerSupported E M m q W (A.ledger s)) (fun _ _ ↦ True)
    (fun b state hstate ↦ ?_) s ⟨hvalid, hinit⟩
  · rw [matrixProgram, OracleProgram.evalState_map]
    exact hh.1.2
  · refine ⟨⟨A.admissible_step state _ hstate.1, A.step_supported q W hW state hstate.1 hstate.2 _ ?_⟩, trivial⟩
    dsimp only [matrixQueries]
    split_ifs
    · exact forwardMatrixRequest_fits E M m p W marks hm i _ _
    · exact transposeMatrixRequest_fits E M m p W marks hm i _ _

theorem evalState_sourceProgram_supported (r : ℕ) (e : E)
    (hp : WordProfile.PrefixFilled p (r * (m + 1)))
    (s : S) (hvalid : A.admissible s) (hs : LedgerSupported E M m p W (A.ledger s)) :
    LedgerSupported E M m p W (A.ledger (OracleProgram.evalState (sourceProgram E M m) A.oracle (r, e) s).2) := by
  have hh := OracleProgram.evalState_fullPass_spec (sourceQueries E M m) (sourceQueries_measurable E M m)
    A.oracle (r, e) (fun s ↦ A.admissible s ∧ LedgerSupported E M m p W (A.ledger s)) (fun _ _ ↦ True)
    (fun t state hstate ↦ ⟨⟨A.admissible_step state _ hstate.1, A.step_supported p W hW state hstate.1 hstate.2 _
      (sourceQueries_fits E M m p W r e hp t)⟩, trivial⟩) s ⟨hvalid, hs⟩
  rw [sourceProgram, OracleProgram.evalState_map]
  exact hh.1.2

theorem evalState_outputMarkProgram_supported
    (c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m)))
    (s : S) (hvalid : A.admissible s) (hs : LedgerSupported E M m p W (A.ledger s)) :
    LedgerSupported E M m p W (A.ledger (OracleProgram.evalState (outputMarkProgram E M m) A.oracle c s).2) ∧
      ∀ t : Vertex M m, (OracleProgram.evalState (outputMarkProgram E M m) A.oracle c s).1 t ∈
        wordSupport t.val (p.words t.val) W := by
  have hh := OracleProgram.evalState_fullPass_spec (fun c t ↦ outputRequest E M m c t)
    (fun t ↦ outputRequest_measurable E M m t) A.oracle c
    (fun s ↦ A.admissible s ∧ LedgerSupported E M m p W (A.ledger s))
    (fun t r ↦ r t ∈ wordSupport t.val (p.words t.val) W)
    (fun t state hstate ↦ ⟨⟨A.admissible_step state _ hstate.1, A.step_supported p W hW state hstate.1 hstate.2 _
      (outputRequest_fits E M m p W c t)⟩, A.inverse_reply_supported p W hW state hstate.1 hstate.2 t _⟩) s ⟨hvalid, hs⟩
  rw [outputMarkProgram, OracleProgram.evalState_map]
  exact ⟨hh.1.2, hh.2⟩

end
end NCConcave16991.BranchOracle
