import NCConcave16991.BranchOracleInterpreter
import NCConcave16991.BranchOracleFlat

/-! # One actual reservoir event gives the entire static transcript equality -/

namespace NCConcave16991.BranchOracle.Reference
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable {D : ℝ} (K : KnownDualDomain (dualDimension (MacroSpaces (ι := Fin n) E M m)) D)
  (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E)
  (d c μ : ℝ) (W : Submodule ℝ E) [W.HasOrthogonalProjection]

def QuerySupported (s : State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (q : OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K) : Prop :=
  ∀ j : Fin M, (Q (macroSite m j)).symm (stateProj (MacroSpaces (ι := Fin n) E M m) j
    (queryGlobal (MacroSpaces (ι := Fin n) E M m) K q)) ∈
      wordSupport (macroSite m j) (s.profile.words (macroSite m j)) W

theorem stepFlat_of_supported (he : ‖e‖ = 1)
    (s : State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (q : OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K)
    (hs : QuerySupported E K Q W s q)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold) :
    StepFlat (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
      releaseThreshold (macroSite (M := M) m) d c μ s q := by
  let s' := step (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
    releaseThreshold (macroSite (M := M) m) d c μ s q
  have hcl := step_closed (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q)
    (incomingSources E Q e) (terminalSources E Q e) releaseThreshold (macroSite (M := M) m) d c μ
    (macroSite_strictMono m M).monotone s q
  have hg := step_words_extend (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q)
    (incomingSources E Q e) (terminalSources E Q e) releaseThreshold (macroSite (M := M) m) d c μ s q
  have hp : ∀ j : Fin M, (Q (macroSite m j)).symm (stateProj (MacroSpaces (ι := Fin n) E M m) j
      (queryGlobal (MacroSpaces (ι := Fin n) E M m) K q)) ∈ wordSupport (macroSite m j) (s'.profile.words (macroSite m j)) W := by
    intro j
    exact hg.support W (macroSite m j) (hs j)
  have hf := macro_inactive_scores_of_closed Q e he s'.profile W s'.released
    (queryGlobal (MacroSpaces (ι := Fin n) E M m) K q) hcl hp hreservoir
  intro j hj
  exact (le_abs_self _).trans_lt (hf j hj)

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) Ω)

def RunSupported (seed : Ω) : ℕ → State (n := n) (MacroSpaces (ι := Fin n) E M m) K → Prop
  | 0, _ => True
  | t + 1, s => match P.next seed s.history with
    | Sum.inl _ => True
    | Sum.inr q => QuerySupported E K Q W s q ∧ RunSupported seed t
        (step (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
          releaseThreshold (macroSite (M := M) m) d c μ s q)

theorem runFlat_of_supported (he : ‖e‖ = 1) (seed : Ω) (t : ℕ)
    (s : State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (hs : RunSupported E K Q e d c μ W P seed t s)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold) :
    RunFlat (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
      releaseThreshold (macroSite (M := M) m) d c μ P seed t s := by
  induction t generalizing s with
  | zero => trivial
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simp only [RunFlat, hn]
    | inr q =>
      simp only [RunSupported, hn] at hs
      simp only [RunFlat, hn]
      exact ⟨stepFlat_of_supported E K Q e d c μ W he s q hs.1 hreservoir, ih _ hs.2⟩

theorem runAux_eq_true_on_common_event (he : ‖e‖ = 1) (seed : Ω) (t : ℕ)
    (s : State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (hs : RunSupported E K Q e d c μ W P seed t s)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold) :
    ((runAux (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        releaseThreshold (macroSite (M := M) m) d c μ P seed t s).1,
      (runAux (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        releaseThreshold (macroSite (M := M) m) d c μ P seed t s).2.history) =
    OraclePolicy.runAux K P (trueComponentAnswer (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q)
      (incomingSources E Q e) (terminalSources E Q e) d c μ) seed t s.history :=
  runAux_eq_true (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
    releaseThreshold (macroSite (M := M) m) d c μ P seed t s
    (runFlat_of_supported E K Q e d c μ W P he seed t s hs hreservoir)

end
end NCConcave16991.BranchOracle.Reference
