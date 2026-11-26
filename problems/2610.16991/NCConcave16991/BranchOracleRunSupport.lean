import NCConcave16991.BranchOracleStepSupport
import NCConcave16991.BranchOracleRunProgram
import NCConcave16991.OracleProgramStateFold

/-! # The complete actual reply-driven run preserves its chronological ledger -/

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
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) Ω)

include hW

def PaddedLedgerInvariant (v : MacroPaddedState E K) (s : S) : Prop :=
  A.admissible s ∧ LedgerSupported E M m v.2.profile W (A.ledger s) ∧
    WordProfile.PrefixFilled v.2.profile (v.2.released * (m + 1))

theorem evalState_mixedRoundProgram_supported (seed : Ω) (v : MacroPaddedState E K) (s : S)
    (hinv : PaddedLedgerInvariant E K A W v s) :
    PaddedLedgerInvariant E K A W
      (OracleProgram.evalState (mixedRoundProgram E K e ρ d c μ P) A.oracle (seed, v) s).1
      (OracleProgram.evalState (mixedRoundProgram E K e ρ d c μ P) A.oracle (seed, v) s).2 := by
  rw [mixedRoundProgram, OracleProgram.evalState_select]
  cases ht : Reference.paddedShouldQuery (MacroSpaces (ι := Fin n) E M m) K P (seed, v) with
  | false =>
    simp only [ht, Bool.false_eq_true, ite_false]
    apply OracleProgram.evalState_spec (stopRoundProgram E K P) A.oracle (seed, v)
      (fun _ _ state ↦ A.admissible state ∧ LedgerSupported E M m v.2.profile W (A.ledger state))
      (fun value state ↦ PaddedLedgerInvariant E K A W value state)
    · intro replies state hs
      exact ⟨hs.1, hs.2, hinv.2.2⟩
    · intro t hlt replies state hs
      exact ⟨A.admissible_step state _ hs.1,
        A.step_supported v.2.profile W hW state hs.1 hs.2 _ (Submodule.zero_mem _)⟩
    · exact ⟨hinv.1, hinv.2.1⟩
  | true =>
    simp only [ht, Bool.true_eq, ite_true, queryRoundProgram, OracleProgram.evalState_map, OracleProgram.evalState_withSeed]
    let a : StepInput E K := (v.2, Reference.paddedQuery (MacroSpaces (ι := Fin n) E M m) K P (seed, v))
    let result := OracleProgram.evalState (componentStepProgram E K e ρ d c μ) A.oracle a s
    have hh := evalState_componentStepProgram_support E K A W hW e ρ d c μ a s hinv.1 hinv.2.1 hinv.2.2
    change A.admissible result.2 ∧ LedgerSupported E M m result.1.profile W (A.ledger result.2) ∧
      WordProfile.PrefixFilled result.1.profile (result.1.released * (m + 1))
    refine ⟨A.evalState_admissible _ a s hinv.1, ?_, ?_⟩
    · rw [hh.2.2.2.1]
      exact hh.1
    · rw [hh.2.2.2.1, hh.2.2.2.2]
      exact hh.2.1

theorem evalState_paddedRoundsProgram_supported (seed : Ω) (budget : ℕ) (s : S)
    (hvalid : A.admissible s) (hs : LedgerSupported E M m WordProfile.root W (A.ledger s)) :
    PaddedLedgerInvariant E K A W
      (OracleProgram.evalState (paddedRoundsProgram E K e ρ d c μ P budget) A.oracle seed s).1
      (OracleProgram.evalState (paddedRoundsProgram E K e ρ d c μ P budget) A.oracle seed s).2 := by
  rw [paddedRoundsProgram, OracleProgram.evalState_castBudget, OracleProgram.evalState_withSeed]
  apply OracleProgram.evalState_fold_invariant
    (fun _ ↦ componentMixedCost (M := M) (m := m)) (fun _ ↦ mixedRoundProgram E K e ρ d c μ P)
    A.oracle seed (fun _ value state ↦ PaddedLedgerInvariant E K A W value state)
  · intro t value state hi
    exact evalState_mixedRoundProgram_supported E K A W hW e ρ d c μ P seed value state hi
  · refine ⟨hvalid, hs, ?_⟩
    simpa only [Reference.paddedInitial, Reference.initial, Nat.zero_mul] using
      (WordProfile.root_prefixFilled (ι := Fin n))

theorem evalState_referenceRunProgram_supported (seed : Ω) (budget : ℕ) (s : S)
    (hvalid : A.admissible s) (hs : LedgerSupported E M m WordProfile.root W (A.ledger s)) :
    let result := OracleProgram.evalState (referenceRunProgram E K e ρ d c μ P budget) A.oracle seed s
    A.admissible result.2 ∧ LedgerSupported E M m result.1.2.profile W (A.ledger result.2) ∧
      WordProfile.PrefixFilled result.1.2.profile (result.1.2.released * (m + 1)) := by
  have hh := evalState_paddedRoundsProgram_supported E K A W hW e ρ d c μ P seed budget s hvalid hs
  rw [referenceRunProgram, OracleProgram.evalState_mapWithSeed]
  exact hh

theorem evalState_referenceMarkedRunProgram_supported (seed : Ω) (budget : ℕ) (s : S)
    (hvalid : A.admissible s) (hs : LedgerSupported E M m WordProfile.root W (A.ledger s)) :
    let result := OracleProgram.evalState (referenceMarkedRunProgram E K e ρ d c μ P budget) A.oracle seed s
    LedgerSupported E M m result.1.1.2.profile W (A.ledger result.2) ∧
      ∀ t : Vertex M m, result.1.2 t ∈ wordSupport t.val (result.1.1.2.profile.words t.val) W := by
  let first := OracleProgram.evalState (referenceRunProgram E K e ρ d c μ P budget) A.oracle seed s
  have hh := evalState_referenceRunProgram_supported E K A W hW e ρ d c μ P seed budget s hvalid hs
  have ho := evalState_outputMarkProgram_supported E M m A first.1.2.profile W hW first.1.1 first.2 hh.1 hh.2.1
  rw [referenceMarkedRunProgram, OracleProgram.evalState_bind, OracleProgram.evalState_mapWithSeed, OracleProgram.evalState_withSeed]
  exact ho

end
end NCConcave16991.BranchOracle
