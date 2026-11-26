import NCConcave16991.BranchOracleStepConsistency

/-! # A consistent actual Gaussian run has full chronological query/output support -/

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
  (W : Submodule ℝ E) (hW : A.Covered W) (e : E) (d c μ : ℝ)
variable (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) Ω)

include hW

theorem fold_querySupported_of_consistent (seed : Ω) (k t : ℕ)
    (v : Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m) K) (s : S)
    (hvalid : A.admissible s) (hs : LedgerSupported E M m v.profile W (A.ledger s))
    (hp : WordProfile.PrefixFilled v.profile (v.released * (m + 1)))
    (hc : OracleProgram.Consistent
      (OracleProgram.fold (fun _ ↦ componentMixedCost (M := M) (m := m))
        (fun _ ↦ mixedRoundProgram E K e releaseThreshold d c μ P) k t)
      A.oracle (replyOracle E M m Q) (seed, ((false, 0), v)) s) :
    Reference.RunSupported E K Q e d c μ W P seed k v := by
  induction k generalizing t v s with
  | zero => trivial
  | succ k ih =>
    change OracleProgram.Consistent
      (OracleProgram.bind (mixedRoundProgram E K e releaseThreshold d c μ P)
        (OracleProgram.withSeed
          (OracleProgram.fold (fun _ ↦ componentMixedCost (M := M) (m := m))
            (fun _ ↦ mixedRoundProgram E K e releaseThreshold d c μ P) k (t + 1))
          (fun a : (Ω × MacroPaddedState E K) × MacroPaddedState E K ↦ (a.1.1, a.2))
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
      A.oracle (replyOracle E M m Q) (seed, ((false, 0), v)) s at hc
    rw [OracleProgram.consistent_bind] at hc
    have hround := hc.1
    cases hn : P.next seed v.history with
    | inl x => simp only [Reference.RunSupported, hn]
    | inr q =>
      have hnext : Reference.paddedNext (MacroSpaces (ι := Fin n) E M m) K P seed ((false, 0), v) = Sum.inr q := by
        simp only [Reference.paddedNext, Bool.false_eq_true, ite_false, hn]
      have hcomponent := component_consistent_of_round_inr E K A e releaseThreshold d c μ Q P seed ((false, 0), v) s q hnext hround
      have hquery := component_querySupported_of_consistent E K A W hW e releaseThreshold d c μ Q (v, q) s hvalid hs hcomponent
      let nextV := Reference.step (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q)
        (incomingSources E Q e) (terminalSources E Q e) releaseThreshold (macroSite (M := M) m) d c μ v q
      let roundResult := OracleProgram.evalState (mixedRoundProgram E K e releaseThreshold d c μ P) A.oracle (seed, ((false, 0), v)) s
      have he : roundResult.1 = ((false, 0), nextV) := by
        calc
          _ = OracleProgram.eval (mixedRoundProgram E K e releaseThreshold d c μ P) (replyOracle E M m Q) (seed, ((false, 0), v)) :=
            OracleProgram.Consistent.eval_eq _ A.oracle (replyOracle E M m Q) _ _ hround
          _ = _ := by rw [eval_mixedRoundProgram]; simp only [Reference.paddedStep, hnext]; rfl
      have hi := evalState_mixedRoundProgram_supported E K A W hW e releaseThreshold d c μ P seed ((false, 0), v) s ⟨hvalid, hs, hp⟩
      change PaddedLedgerInvariant E K A W roundResult.1 roundResult.2 at hi
      rw [he] at hi
      have htail := hc.2
      rw [OracleProgram.consistent_withSeed] at htail
      change OracleProgram.Consistent
        (OracleProgram.fold (fun _ ↦ componentMixedCost (M := M) (m := m))
          (fun _ ↦ mixedRoundProgram E K e releaseThreshold d c μ P) k (t + 1))
        A.oracle (replyOracle E M m Q) (seed, roundResult.1) roundResult.2 at htail
      rw [he] at htail
      have hfuture := ih (t + 1) nextV roundResult.2 hi.1 hi.2.1 hi.2.2 htail
      simp only [Reference.RunSupported, hn]
      exact ⟨hquery, hfuture⟩

theorem referenceRun_supported_of_consistent (seed : Ω) (budget : ℕ) (s : S)
    (hvalid : A.admissible s) (hs : LedgerSupported E M m WordProfile.root W (A.ledger s))
    (hc : OracleProgram.Consistent (referenceRunProgram E K e releaseThreshold d c μ P budget)
      A.oracle (replyOracle E M m Q) seed s) :
    Reference.RunSupported E K Q e d c μ W P seed budget
      (Reference.initial (MacroSpaces (ι := Fin n) E M m) K) := by
  rw [referenceRunProgram, OracleProgram.consistent_mapWithSeed, paddedRoundsProgram,
    OracleProgram.consistent_castBudget, OracleProgram.consistent_withSeed] at hc
  apply fold_querySupported_of_consistent E K A W hW e d c μ Q P seed budget 0
    (Reference.initial (MacroSpaces (ι := Fin n) E M m) K) s hvalid hs
  · simpa only [Reference.initial, Nat.zero_mul] using (WordProfile.root_prefixFilled (ι := Fin n))
  · exact hc

theorem referenceMarkedRun_common_support_of_consistent (seed : Ω) (budget : ℕ) (s : S)
    (hvalid : A.admissible s) (hs : LedgerSupported E M m WordProfile.root W (A.ledger s))
    (hc : OracleProgram.Consistent (referenceMarkedRunProgram E K e releaseThreshold d c μ P budget)
      A.oracle (replyOracle E M m Q) seed s) :
    Reference.RunSupported E K Q e d c μ W P seed budget
        (Reference.initial (MacroSpaces (ι := Fin n) E M m) K) ∧
      ∀ j : Fin M, (Q (macroSite m j)).symm
        (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j
          (Reference.run (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
            releaseThreshold (macroSite (M := M) m) d c μ P seed budget).1) ∈
        wordSupport (macroSite m j)
          ((Reference.run (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
            releaseThreshold (macroSite (M := M) m) d c μ P seed budget).2.profile.words (macroSite m j)) W := by
  have hfull := hc
  rw [referenceMarkedRunProgram, OracleProgram.consistent_bind] at hc
  have hrun := referenceRun_supported_of_consistent E K A W hW e d c μ Q P seed budget s hvalid hs hc.1
  refine ⟨hrun, ?_⟩
  have hout := (evalState_referenceMarkedRunProgram_supported E K A W hW e releaseThreshold d c μ P seed budget s hvalid hs).2
  have he := (OracleProgram.Consistent.eval_eq _ A.oracle (replyOracle E M m Q) seed s hfull).trans
    (eval_referenceMarkedRunProgram E K e releaseThreshold d c μ P Q seed budget)
  rw [he] at hout
  intro j
  have hj := hout (depthVertex M m j (Fin.last (m + 1)))
  change (Q (macroSite m j)).symm (outputMark E M m (macroSite m j) _) ∈ _ at hj
  rw [outputMark_source] at hj
  exact hj

end
end NCConcave16991.BranchOracle
