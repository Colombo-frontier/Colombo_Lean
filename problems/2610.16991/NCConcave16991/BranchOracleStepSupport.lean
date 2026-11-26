import NCConcave16991.BranchOracleBatchSupport
import NCConcave16991.BranchOracleStepProgram
import NCConcave16991.OracleProgramStateBind

/-! # One actual component call preserves the chronological support ledger -/

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
variable {S : Type*} (A : WordEngine (ι := Fin n) E M m S)
  (W : Submodule ℝ E) (hW : A.Covered W) (e : E) (ρ d c μ : ℝ)

include hW

theorem evalState_componentStepProgram_support (a : StepInput E K) (s : S)
    (hvalid : A.admissible s)
    (hs : LedgerSupported E M m a.1.profile W (A.ledger s))
    (hp : WordProfile.PrefixFilled a.1.profile (a.1.released * (m + 1))) :
    let after := Reference.roundUpdate (MacroSpaces (ι := Fin n) E M m) K ρ (macroSite (M := M) m) a
    let result := OracleProgram.evalState (componentStepProgram E K e ρ d c μ) A.oracle a s
    LedgerSupported E M m after.2 W (A.ledger result.2) ∧
      WordProfile.PrefixFilled after.2 (after.1 * (m + 1)) ∧
      InverseMarksSupported E M m a.1.profile W
        (OracleProgram.evalState (queryMarksStepProgram E K) A.oracle a s).1 ∧
      result.1.profile = after.2 ∧ result.1.released = after.1 := by
  let z := queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2
  let marks := OracleProgram.evalState (queryMarkProgram E M m) A.oracle z s
  let actions := OracleProgram.evalState (matrixProgram E M m) A.oracle (a.2.1, marks.1) marks.2
  let after := Reference.roundUpdate (MacroSpaces (ι := Fin n) E M m) K ρ (macroSite (M := M) m) a
  let sources := OracleProgram.evalState (sourceProgram E M m) A.oracle (after.1, e) actions.2
  have hm := evalState_queryMarkProgram_supported E M m A a.1.profile W hW z s hvalid hs
  have hvm := A.evalState_admissible (queryMarkProgram E M m) z s hvalid
  have ha := evalState_matrixProgram_supported E M m A a.1.profile W hW marks.1 hm.2 a.2.1 marks.2 hvm hm.1
  have hva := A.evalState_admissible (matrixProgram E M m) (a.2.1, marks.1) marks.2 hvm
  have hc : LedgerSupported E M m after.2 W (A.ledger actions.2) :=
    fun t ↦ (ha t).trans (wordSupport_mono
      (WordProfile.close_words_extend ρ (macroSite (M := M) m) a.1.released _ t.val) le_rfl)
  have hprefix : WordProfile.PrefixFilled after.2 (after.1 * (m + 1)) :=
    WordProfile.close_prefixFilled ρ a.1.released _
      (hp.mono (WordProfile.matrixScheduleStep_words_extend a.1.profile (fun _ ↦ a.2.1)))
  have hf := evalState_sourceProgram_supported E M m A after.2 W hW after.1 e hprefix actions.2 hva hc
  have he : OracleProgram.evalState (componentStepProgram E K e ρ d c μ) A.oracle a s =
      (finishFromCaches E K ρ d c μ a actions.1 sources.1, sources.2) := by
    simp only [componentStepProgram, markedMatrixProgram, queryMarksStepProgram, sourceFinishProgram,
      OracleProgram.evalState_bind, OracleProgram.evalState_mapWithSeed, OracleProgram.evalState_withSeed]
    rfl
  dsimp only
  rw [he]
  refine ⟨hf, hprefix, ?_, rfl, rfl⟩
  rw [queryMarksStepProgram, OracleProgram.evalState_withSeed]
  exact hm.2

end
end NCConcave16991.BranchOracle
