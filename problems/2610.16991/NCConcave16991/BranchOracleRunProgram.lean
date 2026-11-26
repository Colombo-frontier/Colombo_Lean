import NCConcave16991.BranchOracleStepProgram
import NCConcave16991.BranchOraclePadded

/-! # The entire unrestricted reference policy as a genuine finite mixed program -/

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
variable (e : E) (ρ d c μ : ℝ)
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) Ω)

abbrev MacroPaddedState := Reference.PaddedState (n := n) (MacroSpaces (ι := Fin n) E M m) K
abbrev ReferenceResult := PrimalSpace (primalDimension (MacroSpaces (ι := Fin n) E M m)) ×
  Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m) K

def dummyMixedRequest : MixedRequest (ι := Fin n) E M m := ⟨0, Sum.inl 0⟩

def queryRoundProgram : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (MacroPaddedState E K) (Ω × MacroPaddedState E K) (componentMixedCost (M := M) (m := m)) :=
  OracleProgram.map
    (OracleProgram.withSeed (componentStepProgram E K e ρ d c μ)
      (fun a : Ω × MacroPaddedState E K ↦
        (a.2.2, Reference.paddedQuery (MacroSpaces (ι := Fin n) E M m) K P a))
      ((measurable_snd.comp measurable_snd).prodMk
        (Reference.paddedQuery_measurable (MacroSpaces (ι := Fin n) E M m) K P)))
    (fun s ↦ ((false, 0), s)) ((measurable_const.prodMk measurable_const).prodMk measurable_id)

def stopRoundProgram : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (MacroPaddedState E K) (Ω × MacroPaddedState E K) (componentMixedCost (M := M) (m := m)) :=
  OracleProgram.ignoreQueries _ (fun _ ↦ dummyMixedRequest (M := M) (m := m) E) measurable_const
    (Reference.paddedStop (MacroSpaces (ι := Fin n) E M m) K P)
    (Reference.paddedStop_measurable (MacroSpaces (ι := Fin n) E M m) K P)

def mixedRoundProgram : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (MacroPaddedState E K) (Ω × MacroPaddedState E K) (componentMixedCost (M := M) (m := m)) :=
  OracleProgram.select (Reference.paddedShouldQuery (MacroSpaces (ι := Fin n) E M m) K P)
    (Reference.paddedShouldQuery_measurable (MacroSpaces (ι := Fin n) E M m) K P)
    (fun b ↦ if b then queryRoundProgram E K e ρ d c μ P else stopRoundProgram E K P)

theorem eval_mixedRoundProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (seed : Ω) (s : MacroPaddedState E K) :
    OracleProgram.eval (mixedRoundProgram E K e ρ d c μ P) (replyOracle E M m Q) (seed, s) =
      Reference.paddedStep (MacroSpaces (ι := Fin n) E M m) K P (macroBranches E Q)
        (incomingSources E Q e) (terminalSources E Q e) ρ (macroSite (M := M) m) d c μ seed s := by
  rw [mixedRoundProgram, OracleProgram.eval_select]
  cases hn : Reference.paddedNext (MacroSpaces (ι := Fin n) E M m) K P seed s with
  | inl x =>
    simp only [Reference.paddedShouldQuery, hn, Sum.elim_inl, Bool.false_eq_true, ite_false,
      stopRoundProgram, OracleProgram.eval_ignoreQueries, Reference.paddedStop, Reference.paddedStep]
    rfl
  | inr q =>
    simp only [Reference.paddedShouldQuery, hn, Sum.elim_inr, Bool.true_eq, ite_true,
      queryRoundProgram, OracleProgram.eval_map, OracleProgram.eval_withSeed,
      Reference.paddedQuery, hn, eval_componentStepProgram, Reference.paddedStep]
    rfl

def paddedRoundsProgram (budget : ℕ) : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (MacroPaddedState E K) Ω (budget * componentMixedCost (M := M) (m := m)) :=
  OracleProgram.castBudget
    (OracleProgram.withSeed
      (OracleProgram.fold (fun _ ↦ componentMixedCost (M := M) (m := m))
        (fun _ ↦ mixedRoundProgram E K e ρ d c μ P) budget 0)
      (fun seed ↦ (seed, Reference.paddedInitial (MacroSpaces (ι := Fin n) E M m) K))
      (measurable_id.prodMk measurable_const))
    (OracleProgram.foldBudget_constant _ budget 0)

theorem eval_paddedRoundsProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (seed : Ω) (budget : ℕ) :
    OracleProgram.eval (paddedRoundsProgram E K e ρ d c μ P budget) (replyOracle E M m Q) seed =
      Reference.paddedExecute (MacroSpaces (ι := Fin n) E M m) K P (macroBranches E Q)
        (incomingSources E Q e) (terminalSources E Q e) ρ (macroSite (M := M) m) d c μ seed budget
        (Reference.paddedInitial (MacroSpaces (ι := Fin n) E M m) K) := by
  rw [paddedRoundsProgram, OracleProgram.eval_castBudget, OracleProgram.eval_withSeed, OracleProgram.eval_fold]
  simp_rw [eval_mixedRoundProgram]
  exact Reference.executeBlocks_eq_paddedExecute _ _ _ _ _ _ _ _ _ _ _ seed budget 0 _

def referenceRunProgram (budget : ℕ) : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (ReferenceResult E K) Ω (budget * componentMixedCost (M := M) (m := m)) :=
  OracleProgram.mapWithSeed (paddedRoundsProgram E K e ρ d c μ P budget)
    (Reference.finishPadded (MacroSpaces (ι := Fin n) E M m) K P)
    (Reference.finishPadded_measurable (MacroSpaces (ι := Fin n) E M m) K P)

theorem eval_referenceRunProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (seed : Ω) (budget : ℕ) :
    OracleProgram.eval (referenceRunProgram E K e ρ d c μ P budget) (replyOracle E M m Q) seed =
      Reference.run (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ P seed budget := by
  rw [referenceRunProgram, OracleProgram.eval_mapWithSeed, eval_paddedRoundsProgram]
  exact Reference.finishPadded_execute_eq_runAux _ _ _ _ _ _ _ _ _ _ _ seed budget _

def fullMixedCost (budget : ℕ) : ℕ := budget * componentMixedCost (M := M) (m := m) + (M * (m + 1) + 1)

def referenceMarkedRunProgram (budget : ℕ) : OracleProgram.Fixed (MixedRequest (ι := Fin n) E M m) (MixedReply (ι := Fin n) E M m)
    (ReferenceResult E K × MixedReply (ι := Fin n) E M m) Ω (fullMixedCost (M := M) (m := m) budget) :=
  OracleProgram.bind (referenceRunProgram E K e ρ d c μ P budget)
    (OracleProgram.mapWithSeed
      (OracleProgram.withSeed (outputMarkProgram E M m)
        (fun a : Ω × ReferenceResult E K ↦ a.2.1) (measurable_fst.comp measurable_snd))
      (fun a marks ↦ (a.2, marks)) ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem eval_referenceMarkedRunProgram
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (seed : Ω) (budget : ℕ) :
    OracleProgram.eval (referenceMarkedRunProgram E K e ρ d c μ P budget) (replyOracle E M m Q) seed =
      (Reference.run (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ P seed budget,
       fun t : Vertex M m ↦ (Q t.val).symm (outputMark E M m t.val
         (Reference.run (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
           ρ (macroSite (M := M) m) d c μ P seed budget).1)) := by
  rw [referenceMarkedRunProgram, OracleProgram.eval_bind, OracleProgram.eval_mapWithSeed,
    OracleProgram.eval_withSeed, eval_outputMarkProgram, eval_referenceRunProgram]

theorem fullMixedCost_eq (budget : ℕ) : fullMixedCost (M := M) (m := m) budget =
    budget * (8 * (M * (m + 1)) + 6) + M * (m + 1) + 1 := by
  simp only [fullMixedCost, componentMixedCost, queryMarkCount, matrixRequestCount]
  ring

end
end NCConcave16991.BranchOracle
