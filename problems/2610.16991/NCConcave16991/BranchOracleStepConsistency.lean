import NCConcave16991.BranchOracleStepSupport
import NCConcave16991.BranchOracleRunSupport
import NCConcave16991.OracleProgramStateConsistencyBind
import NCConcave16991.OracleProgramStateConsistencyTransform

/-! # Actual reply-cache consistency identifies the supported query marks -/

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
variable (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)

include hW

theorem component_querySupported_of_consistent (a : StepInput E K) (s : S)
    (hvalid : A.admissible s) (hs : LedgerSupported E M m a.1.profile W (A.ledger s))
    (hc : OracleProgram.Consistent (componentStepProgram E K e ρ d c μ) A.oracle (replyOracle E M m Q) a s) :
    Reference.QuerySupported E K Q W a.1 a.2 := by
  rw [componentStepProgram, OracleProgram.consistent_bind] at hc
  have hmarked := hc.1
  rw [markedMatrixProgram, OracleProgram.consistent_bind] at hmarked
  have hmarks := hmarked.1
  have he := OracleProgram.Consistent.eval_eq (queryMarksStepProgram E K) A.oracle (replyOracle E M m Q) a s hmarks
  rw [queryMarksStepProgram, OracleProgram.evalState_withSeed, OracleProgram.eval_withSeed, eval_queryMarkProgram] at he
  have hm := (evalState_queryMarkProgram_supported E M m A a.1.profile W hW
    (queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2) s hvalid hs).2
  rw [he] at hm
  exact querySupported_of_inverseMarks E M m K Q a.1 a.2 W hm

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) Ω)

omit hW in
theorem component_consistent_of_round_inr (seed : Ω) (v : MacroPaddedState E K) (s : S)
    (q : OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K)
    (hn : Reference.paddedNext (MacroSpaces (ι := Fin n) E M m) K P seed v = Sum.inr q)
    (hc : OracleProgram.Consistent (mixedRoundProgram E K e ρ d c μ P) A.oracle (replyOracle E M m Q) (seed, v) s) :
    OracleProgram.Consistent (componentStepProgram E K e ρ d c μ) A.oracle (replyOracle E M m Q) (v.2, q) s := by
  rw [mixedRoundProgram, OracleProgram.consistent_select] at hc
  have ht : Reference.paddedShouldQuery (MacroSpaces (ι := Fin n) E M m) K P (seed, v) = true := by
    simp only [Reference.paddedShouldQuery, hn, Sum.elim_inr]
  rw [ht, if_pos rfl, queryRoundProgram, OracleProgram.consistent_map, OracleProgram.consistent_withSeed] at hc
  simpa only [Reference.paddedQuery, hn, Sum.elim_inr, id_eq] using hc

end
end NCConcave16991.BranchOracle
