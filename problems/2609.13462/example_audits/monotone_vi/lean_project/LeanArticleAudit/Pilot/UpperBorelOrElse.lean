import LeanArticleAudit.Pilot.UpperBorelCallOutcome

/-!
# Borel closure of finite capped fallback

An arbitrary `ExactJetProgram` has nonmeasurable continuations, so fallback
closure is proved from the stronger joint replay-outcome invariant.  The first
program is locally capped before fallback; induction on that finite cap makes
the stopping split auditable without any padding transcript.
-/

open Set MeasureTheory

namespace LeanArticleAudit.Pilot

noncomputable section

namespace ExactJetProgram

universe u

variable {X Answer Output P : Type u}
  [MeasurableSpace X] [MeasurableSpace Answer]
  [MeasurableSpace Output] [MeasurableSpace P]

private theorem measurableSet_option_none :
    MeasurableSet ({none} : Set (Option Output)) := by
  have hset : MeasurableSet
      (Set.range (Sum.inr : PUnit → Output ⊕ PUnit)) :=
    measurableSet_range_inr
  have heq : ({none} : Set (Option Output)) =
      (Equiv.optionEquivSumPUnit Output) ⁻¹'
        Set.range (Sum.inr : PUnit → Output ⊕ PUnit) := by
    ext value
    cases value <;> simp
  rw [heq]
  exact hset.preimage measurable_optionEquivSumPUnit

private theorem measurableSet_outcome_none :
    MeasurableSet ({Sum.inl none} : Set (Sum (Option Output) X)) := by
  have h : MeasurableSet
      (Sum.inl '' ({none} : Set (Option Output)) :
        Set (Sum (Option Output) X)) :=
    (measurableSet_option_none (Output := Output)).inl_image
  simpa using h

private def emptyTranscript : Fin 0 → X × Answer := fun i => Fin.elim0 i

private theorem measurable_emptyHistory
    {Q : Type u} [MeasurableSpace Q] :
    Measurable (fun q : Q =>
      (q, emptyTranscript (X := X) (Answer := Answer))) :=
  measurable_id.prodMk measurable_const

/-- Joint replay outcomes are closed under trying a locally capped first
program and running a fallback exactly when that first program reports
failure.  The dummy point is used only in a counterfactual transcript when
forming the measurable continuation family; replay never observes that point
coordinate.

This is deliberately a finite-cap theorem.  It makes no false claim that an
uncapped arbitrary stopping tree admits a globally measurable stopping-time
split. -/
theorem IsJointlyBorelOutcome.orElse_locallyCapped
    {first fallback : P → ExactJetProgram X Answer Output}
    (hfirst : IsJointlyBorelOutcome first)
    (hfallback : IsJointlyBorelOutcome fallback)
    (dummy : X) (cap : ℕ) :
    IsJointlyBorelOutcome (fun p =>
      ((first p).locallyCapped cap).orElse (fallback p)) := by
  induction cap generalizing P with
  | zero =>
      intro n
      let emptyHistory : Fin 0 → X × Answer := fun i => Fin.elim0 i
      let initial : P → Sum (Option Output) X := fun p =>
        replayOutcomeAction (first p) emptyHistory
      have hinitial : Measurable initial :=
        (hfirst 0).comp (measurable_emptyHistory (X := X) (Answer := Answer))
      let failure : Set P :=
        initial ⁻¹' ({Sum.inl none} : Set (Sum (Option Output) X)) ∪
          initial ⁻¹' Set.range (Sum.inr : X → Sum (Option Output) X)
      have hfailure : MeasurableSet failure :=
        (measurableSet_outcome_none (X := X) (Output := Output)).preimage
            hinitial |>.union (measurableSet_range_inr.preimage hinitial)
      have hfailure' : MeasurableSet
          {z : P × (Fin n → X × Answer) | z.1 ∈ failure} :=
        hfailure.preimage measurable_fst
      have hinitial' : Measurable (fun z : P × (Fin n → X × Answer) =>
          initial z.1) := hinitial.comp measurable_fst
      letI : DecidablePred (fun z : P × (Fin n → X × Answer) =>
        z.1 ∈ failure) := Classical.decPred _
      have hite : Measurable (fun z : P × (Fin n → X × Answer) =>
          if z.1 ∈ failure then replayOutcomeAction (fallback z.1) z.2
          else initial z.1) :=
        Measurable.ite hfailure' (hfallback n) hinitial'
      convert hite using 1
      funext z
      cases hprog : first z.1 with
      | halt result =>
          cases result with
          | none => simp [failure, initial, emptyHistory, hprog,
              ExactJetProgram.locallyCapped, ExactJetProgram.orElse,
              replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
          | some value => simp [failure, initial, emptyHistory, hprog,
              ExactJetProgram.locallyCapped, ExactJetProgram.orElse,
              replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
      | query point next =>
          simp [failure, initial, emptyHistory, hprog,
            ExactJetProgram.locallyCapped, ExactJetProgram.orElse,
            replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
  | succ cap ih =>
      have htailFirst : IsJointlyBorelOutcome (fun z : P × Answer =>
          ExactJetProgram.afterFirstAnswer (first z.1) z.2) :=
        hfirst.afterFirstAnswer dummy
      have htailFallback : IsJointlyBorelOutcome (fun z : P × Answer =>
          fallback z.1) :=
        hfallback.compParameter Prod.fst measurable_fst
      have hrecursive : IsJointlyBorelOutcome (fun z : P × Answer =>
          (((ExactJetProgram.afterFirstAnswer (first z.1) z.2).locallyCapped cap).orElse
            (fallback z.1))) :=
        ih (first := fun z : P × Answer =>
              ExactJetProgram.afterFirstAnswer (first z.1) z.2)
          (fallback := fun z : P × Answer => fallback z.1)
          htailFirst htailFallback
      intro n
      let emptyHistory : Fin 0 → X × Answer := fun i => Fin.elim0 i
      let initial : P → Sum (Option Output) X := fun p =>
        replayOutcomeAction (first p) emptyHistory
      have hinitial : Measurable initial :=
        (hfirst 0).comp (measurable_emptyHistory (X := X) (Answer := Answer))
      let failed : Set P :=
        initial ⁻¹' ({Sum.inl none} : Set (Sum (Option Output) X))
      let querying : Set P :=
        initial ⁻¹' Set.range (Sum.inr : X → Sum (Option Output) X)
      have hfailed : MeasurableSet failed :=
        (measurableSet_outcome_none (X := X) (Output := Output)).preimage hinitial
      have hquerying : MeasurableSet querying :=
        measurableSet_range_inr.preimage hinitial
      cases n with
      | zero =>
          have hfailed' : MeasurableSet
              {z : P × (Fin 0 → X × Answer) | z.1 ∈ failed} :=
            hfailed.preimage measurable_fst
          have hinitial' : Measurable (fun z : P × (Fin 0 → X × Answer) =>
              initial z.1) := hinitial.comp measurable_fst
          letI : DecidablePred (fun z : P × (Fin 0 → X × Answer) =>
            z.1 ∈ failed) := Classical.decPred _
          have hite : Measurable (fun z : P × (Fin 0 → X × Answer) =>
              if z.1 ∈ failed then replayOutcomeAction (fallback z.1) z.2
              else initial z.1) :=
            Measurable.ite hfailed' (hfallback 0) hinitial'
          convert hite using 1
          funext z
          cases hprog : first z.1 with
          | halt result =>
              cases result <;> simp [failed, initial, emptyHistory, hprog,
                ExactJetProgram.locallyCapped, ExactJetProgram.orElse,
                replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
          | query point next =>
              simp [failed, initial, emptyHistory, hprog,
                ExactJetProgram.locallyCapped, ExactJetProgram.orElse,
                replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
      | succ n =>
          have hfailed' : MeasurableSet
              {z : P × (Fin (n + 1) → X × Answer) | z.1 ∈ failed} :=
            hfailed.preimage measurable_fst
          have hquerying' : MeasurableSet
              {z : P × (Fin (n + 1) → X × Answer) | z.1 ∈ querying} :=
            hquerying.preimage measurable_fst
          have hinitial' : Measurable
              (fun z : P × (Fin (n + 1) → X × Answer) => initial z.1) :=
            hinitial.comp measurable_fst
          have harg : Measurable (fun z :
              P × (Fin (n + 1) → X × Answer) =>
              ((z.1, (z.2 0).2), fun i : Fin n => z.2 i.succ)) := by
            fun_prop
          have hrecurse : Measurable (fun z :
              P × (Fin (n + 1) → X × Answer) =>
              replayOutcomeAction
                (((ExactJetProgram.afterFirstAnswer
                    (first z.1) (z.2 0).2).locallyCapped cap).orElse
                  (fallback z.1))
                (fun i : Fin n => z.2 i.succ)) :=
            (hrecursive n).comp harg
          letI : DecidablePred (fun z : P × (Fin (n + 1) → X × Answer) =>
            z.1 ∈ failed) := Classical.decPred _
          letI : DecidablePred (fun z : P × (Fin (n + 1) → X × Answer) =>
            z.1 ∈ querying) := Classical.decPred _
          have hqueryOrInitial : Measurable (fun z :
              P × (Fin (n + 1) → X × Answer) =>
              if z.1 ∈ querying then
                replayOutcomeAction
                  (((ExactJetProgram.afterFirstAnswer
                      (first z.1) (z.2 0).2).locallyCapped cap).orElse
                    (fallback z.1))
                  (fun i : Fin n => z.2 i.succ)
              else initial z.1) :=
            Measurable.ite hquerying' hrecurse hinitial'
          have hite : Measurable (fun z :
              P × (Fin (n + 1) → X × Answer) =>
              if z.1 ∈ failed then replayOutcomeAction (fallback z.1) z.2
              else if z.1 ∈ querying then
                replayOutcomeAction
                  (((ExactJetProgram.afterFirstAnswer
                      (first z.1) (z.2 0).2).locallyCapped cap).orElse
                    (fallback z.1))
                  (fun i : Fin n => z.2 i.succ)
              else initial z.1) :=
            Measurable.ite hfailed' (hfallback (n + 1)) hqueryOrInitial
          convert hite using 1
          funext z
          cases hprog : first z.1 with
          | halt result =>
              cases result <;> simp [failed, querying, initial, emptyHistory,
                hprog, ExactJetProgram.locallyCapped, ExactJetProgram.orElse,
                replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
          | query point next =>
              have hnotFailed : z.1 ∉ failed := by
                simp [failed, initial, emptyHistory, hprog,
                  replayOutcomeAction, residualAfterHistory,
                  residualAfterAnswers]
              have hqueryingNow : z.1 ∈ querying := by
                simp [querying, initial, emptyHistory, hprog,
                  replayOutcomeAction, residualAfterHistory,
                  residualAfterAnswers]
              simp [hnotFailed, hqueryingNow, failed, querying, initial,
                emptyHistory, hprog,
                ExactJetProgram.locallyCapped, ExactJetProgram.orElse,
                replayOutcomeAction_query_succ, residualAfterHistory,
                residualAfterAnswers, ExactJetProgram.afterFirstAnswer]

end ExactJetProgram

end

end LeanArticleAudit.Pilot
