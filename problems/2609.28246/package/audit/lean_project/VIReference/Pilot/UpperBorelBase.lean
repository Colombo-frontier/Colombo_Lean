import VIReference.Pilot.UpperBorelHalving
import VIReference.Pilot.UpperBorelCallOutcome
import VIReference.Pilot.UpperBorelOrElse
import VIReference.Pilot.UpperBaseStrongClaim

/-!
# Borel replay closure for base trials

The key lemma is a continuation-passing strengthening of the whole halving
tree.  It makes the subsequent base-trial recursion compositional while
retaining the original executable program definition.
-/

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace VIReference.Pilot

noncomputable section

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ExactJetProgram

variable {X Answer Output : Type*}
  [MeasurableSpace X] [MeasurableSpace Answer]

/-- Associativity of the free exact-query program bind. -/
theorem bind_assoc_eq {A B C : Type*}
    (program : ExactJetProgram X Answer A)
    (next : A → ExactJetProgram X Answer B)
    (last : B → ExactJetProgram X Answer C) :
    (program.bind next).bind last =
      program.bind (fun a => (next a).bind last) := by
  induction program with
  | halt result => cases result <;> rfl
  | query point more ih =>
      simp only [bind]
      congr 1
      funext answer
      exact ih answer

private def actionAtCap (fallback : X) : Sum X X → Sum X X :=
  Sum.elim Sum.inl (fun _ => Sum.inl fallback)

private theorem measurable_actionAtCap (fallback : X) :
    Measurable (actionAtCap fallback) :=
  measurable_inl.sumElim measurable_const

/-- Action measurability alone is stable under installing a finite hard cap.
Before the cap the replay action is unchanged; exactly at the cap, a residual
query is measurably converted to the explicit failure output. -/
theorem IsBorelAction.locallyCappedAction
    {finish : Option Output → X} {program : ExactJetProgram X Answer Output}
    (h : IsBorelAction finish program) (cap : ℕ) (n : ℕ) (hn : n ≤ cap) :
    Measurable (fun history : Fin n → X × Answer =>
      replayAction finish (program.locallyCapped cap) history) := by
  by_cases hlt : n < cap
  · have heq : (fun history : Fin n → X × Answer =>
        replayAction finish (program.locallyCapped cap) history) =
        fun history => replayAction finish program history := by
      funext history
      unfold replayAction residualAfterHistory
      rw [residualAfterAnswers_locallyCapped_of_length_le program cap _ (by simpa)]
      cases hres : residualAfterAnswers program
          (List.ofFn fun i => (history i).2) with
      | halt result => simp [hres, ExactJetProgram.locallyCapped]
      | query point next =>
          obtain ⟨left, hleft⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
          have hlen : (List.ofFn fun i => (history i).2).length = n := by simp
          rw [hlen, hleft]
          simp [hres, ExactJetProgram.locallyCapped]
    rw [heq]
    exact h n
  · have hncap : n = cap := by omega
    subst n
    have heq : (fun history : Fin cap → X × Answer =>
        replayAction finish (program.locallyCapped cap) history) =
        actionAtCap (finish none) ∘
          (fun history => replayAction finish program history) := by
      funext history
      unfold replayAction residualAfterHistory
      rw [residualAfterAnswers_locallyCapped_of_length_le program cap _ (by simp)]
      cases hres : residualAfterAnswers program
          (List.ofFn fun i => (history i).2) <;>
        simp [hres, ExactJetProgram.locallyCapped, actionAtCap]
    rw [heq]
    exact (measurable_actionAtCap (finish none)).comp (h cap)

private def outcomeAtCap [MeasurableSpace Output] :
    Sum (Option Output) X → Sum (Option Output) X :=
  Sum.elim Sum.inl (fun _ => Sum.inl none)

private theorem measurable_outcomeAtCap [MeasurableSpace Output] :
    Measurable (outcomeAtCap :
      Sum (Option Output) X → Sum (Option Output) X) :=
  measurable_inl.sumElim measurable_const

private theorem residualAfterAnswers_locallyCapped_take
    (program : ExactJetProgram X Answer Output) (cap : ℕ)
    (answers : List Answer) :
    residualAfterAnswers (program.locallyCapped cap) answers =
      residualAfterAnswers (program.locallyCapped cap) (answers.take cap) := by
  induction cap generalizing program answers with
  | zero =>
      cases program <;> cases answers <;>
        simp [ExactJetProgram.locallyCapped, residualAfterAnswers]
  | succ cap ih =>
      cases program with
      | halt result => simp [ExactJetProgram.locallyCapped, residualAfterAnswers]
      | query point next =>
          cases answers with
          | nil => simp [ExactJetProgram.locallyCapped, residualAfterAnswers]
          | cons answer answers =>
              simpa [ExactJetProgram.locallyCapped, residualAfterAnswers] using
                ih (next answer) answers

/-- Raw terminal/query measurability is stable under a finite hard cap, for
all transcript lengths (including counterfactual histories beyond the cap). -/
theorem IsBorelOutcome.locallyCappedOutcome [MeasurableSpace Output]
    {program : ExactJetProgram X Answer Output} (h : IsBorelOutcome program)
    (cap : ℕ) : IsBorelOutcome (program.locallyCapped cap) := by
  intro n
  by_cases hn : n ≤ cap
  · by_cases hlt : n < cap
    · have heq : (fun history : Fin n → X × Answer =>
          replayOutcomeAction (program.locallyCapped cap) history) =
          fun history => replayOutcomeAction program history := by
        funext history
        unfold replayOutcomeAction residualAfterHistory
        rw [residualAfterAnswers_locallyCapped_of_length_le program cap _ (by simpa)]
        cases hres : residualAfterAnswers program
            (List.ofFn fun i => (history i).2) with
        | halt result => simp [hres, ExactJetProgram.locallyCapped]
        | query point next =>
            obtain ⟨left, hleft⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
            have hlen : (List.ofFn fun i => (history i).2).length = n := by simp
            rw [hlen, hleft]
            simp [hres, ExactJetProgram.locallyCapped]
      rw [heq]
      exact h n
    · have hncap : n = cap := by omega
      subst n
      have heq : (fun history : Fin cap → X × Answer =>
          replayOutcomeAction (program.locallyCapped cap) history) =
          outcomeAtCap ∘ (fun history => replayOutcomeAction program history) := by
        funext history
        unfold replayOutcomeAction residualAfterHistory
        rw [residualAfterAnswers_locallyCapped_of_length_le program cap _ (by simp)]
        cases hres : residualAfterAnswers program
            (List.ofFn fun i => (history i).2) <;>
          simp [hres, ExactJetProgram.locallyCapped, outcomeAtCap]
      rw [heq]
      exact measurable_outcomeAtCap.comp (h cap)
  · have hcap : cap ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have heq : (fun history : Fin n → X × Answer =>
        replayOutcomeAction (program.locallyCapped cap) history) =
        fun history => replayOutcomeAction (program.locallyCapped cap)
          (restrictTranscript history hcap) := by
      funext history
      unfold replayOutcomeAction residualAfterHistory
      rw [residualAfterAnswers_locallyCapped_take]
      have hof : List.ofFn
          (fun i : Fin cap => (restrictTranscript history hcap i).2) =
          (List.ofFn fun i : Fin n => (history i).2).take cap := by
        rw [← Fin.ofFn_take_eq_take_ofFn hcap
          (fun i : Fin n => (history i).2)]
        rfl
      rw [hof]
    rw [heq]
    exact ((h.locallyCappedOutcome cap) cap).comp (by
      refine measurable_pi_lambda _ fun i => ?_
      exact measurable_pi_apply
        (⟨i.1, lt_of_lt_of_le i.2 hcap⟩ : Fin n))

/-- Parameter-uniform version of `locallyCappedOutcome`. -/
theorem IsJointlyBorelOutcome.locallyCappedOutcome
    {P : Type*} [MeasurableSpace P] [MeasurableSpace Output]
    {program : P → ExactJetProgram X Answer Output}
    (h : IsJointlyBorelOutcome program) (cap : ℕ) :
    IsJointlyBorelOutcome (fun p => (program p).locallyCapped cap) := by
  intro n
  by_cases hn : n ≤ cap
  · by_cases hlt : n < cap
    · have heq : (fun z : P × (Fin n → X × Answer) =>
          replayOutcomeAction ((program z.1).locallyCapped cap) z.2) =
          fun z => replayOutcomeAction (program z.1) z.2 := by
        funext z
        unfold replayOutcomeAction residualAfterHistory
        rw [residualAfterAnswers_locallyCapped_of_length_le (program z.1) cap _
          (by simpa)]
        cases hres : residualAfterAnswers (program z.1)
            (List.ofFn fun i => (z.2 i).2) with
        | halt result => simp [hres, ExactJetProgram.locallyCapped]
        | query point next =>
            obtain ⟨left, hleft⟩ := Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
            have hlen : (List.ofFn fun i => (z.2 i).2).length = n := by simp
            rw [hlen, hleft]
            simp [hres, ExactJetProgram.locallyCapped]
      rw [heq]
      exact h n
    · have hncap : n = cap := by omega
      subst n
      have heq : (fun z : P × (Fin cap → X × Answer) =>
          replayOutcomeAction ((program z.1).locallyCapped cap) z.2) =
          outcomeAtCap ∘ (fun z => replayOutcomeAction (program z.1) z.2) := by
        funext z
        unfold replayOutcomeAction residualAfterHistory
        rw [residualAfterAnswers_locallyCapped_of_length_le (program z.1) cap _
          (by simp)]
        cases hres : residualAfterAnswers (program z.1)
            (List.ofFn fun i => (z.2 i).2) <;>
          simp [hres, ExactJetProgram.locallyCapped, outcomeAtCap]
      rw [heq]
      exact measurable_outcomeAtCap.comp (h cap)
  · have hcap : cap ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have heq : (fun z : P × (Fin n → X × Answer) =>
        replayOutcomeAction ((program z.1).locallyCapped cap) z.2) =
        fun z => replayOutcomeAction ((program z.1).locallyCapped cap)
          (restrictTranscript z.2 hcap) := by
      funext z
      unfold replayOutcomeAction residualAfterHistory
      rw [residualAfterAnswers_locallyCapped_take]
      have hof : List.ofFn
          (fun i : Fin cap => (restrictTranscript z.2 hcap i).2) =
          (List.ofFn fun i : Fin n => (z.2 i).2).take cap := by
        rw [← Fin.ofFn_take_eq_take_ofFn hcap
          (fun i : Fin n => (z.2 i).2)]
        rfl
      rw [hof]
    rw [heq]
    exact ((h.locallyCappedOutcome cap) cap).comp (by
      show Measurable (fun z : P × (Fin n → X × Answer) =>
        (z.1, restrictTranscript z.2 hcap))
      apply Measurable.prodMk measurable_fst
      refine measurable_pi_lambda _ fun i => ?_
      exact (measurable_pi_apply
        (⟨i.1, lt_of_lt_of_le i.2 hcap⟩ : Fin n)).comp measurable_snd)

end ExactJetProgram

section HalvingCPS

variable (data : VIPublicData E) (mu : ℝ)

/-- Whole-tree Borel closure for a Halve call followed by an arbitrary Borel
continuation.  This is stronger than merely observing the Halve result. -/
theorem halvingProgramAux_bind_isJointlyBorelAction
    {Q : Type v} {Output : Type w} [MeasurableSpace Q]
    (finish : Option Output → data.X)
    (next : Q × HalvingOutput data → ExactJetProgram data.X
      (SymmetricExactJet E data.p) Output)
    (hnext : ExactJetProgram.IsJointlyBorelAction finish next)
    (remaining : ℕ) :
    ExactJetProgram.IsJointlyBorelAction finish
      (fun qs : Q × HalvingBorelState data =>
        (halvingProgramAux data mu remaining qs.2.1 qs.2.2.1 qs.2.2.2).bind
          (fun out => next (qs.1, out))) := by
  induction remaining with
  | zero =>
      have hparam : Measurable (fun qs : Q × HalvingBorelState data =>
          (qs.1, halvingTerminal data qs.2)) :=
        measurable_fst.prodMk ((measurable_halvingTerminal data).comp measurable_snd)
      simpa [halvingProgramAux, halvingTerminal, ExactJetProgram.bind] using
        hnext.compParameter _ hparam
  | succ remaining ih =>
      let P := Q × HalvingBorelState data
      let A := P × SymmetricExactJet E data.p
      let model : A → data.X × E := fun a =>
        knownModelStep data a.1.2.1 a.2
      have hmodel : Measurable model := by
        exact (measurable_knownModelStep_componentwise data).comp
          ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
            measurable_snd)
      let earlySet : Set A := {a | (model a).1 = a.1.2.1}
      have hearlySet : MeasurableSet earlySet :=
        measurableSet_eq_fun (measurable_fst.comp hmodel)
          (measurable_fst.comp (measurable_snd.comp measurable_fst))
      let earlyProgram : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) Output := fun a =>
        next (a.1.1, halvingEarly data (a.1.2, a.2))
      have hearlyProgram :
          ExactJetProgram.IsJointlyBorelAction finish earlyProgram := by
        exact hnext.compParameter
          (fun a : A => (a.1.1, halvingEarly data (a.1.2, a.2)))
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_halvingEarly data).comp
              ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      let lateTail : (A × SymmetricExactJet E data.p) →
          ExactJetProgram data.X (SymmetricExactJet E data.p) Output := fun a =>
        (halvingProgramAux data mu remaining
          (halvingNextState data ((a.1.1.2, a.1.2), a.2)).1
          (halvingNextState data ((a.1.1.2, a.1.2), a.2)).2.1
          (halvingNextState data ((a.1.1.2, a.1.2), a.2)).2.2).bind
            (fun out => next (a.1.1.1, out))
      have hlateTail :
          ExactJetProgram.IsJointlyBorelAction finish lateTail := by
        exact ih.compParameter
          (fun a : A × SymmetricExactJet E data.p =>
            (a.1.1.1, halvingNextState data ((a.1.1.2, a.1.2), a.2)))
          ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            ((measurable_halvingNextState data).comp
              (((measurable_snd.comp (measurable_fst.comp
                  measurable_fst)).prodMk
                (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
      let lateProgram : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) Output := fun a =>
        .query (model a).1 (fun jety => lateTail (a, jety))
      have hlateProgram :
          ExactJetProgram.IsJointlyBorelAction finish lateProgram :=
        ExactJetProgram.isJointlyBorelAction_query finish
          (fun a : A => (model a).1) lateTail
          (measurable_fst.comp hmodel) hlateTail
      let afterFirst : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) Output :=
        ExactJetProgram.actionPiecewise earlySet earlyProgram lateProgram
      have hafterFirst :
          ExactJetProgram.IsJointlyBorelAction finish afterFirst :=
        ExactJetProgram.isJointlyBorelAction_piecewise finish earlySet hearlySet
          earlyProgram lateProgram hearlyProgram hlateProgram
      have hwhole := ExactJetProgram.isJointlyBorelAction_query finish
        (fun qs : P => qs.2.1)
        (fun a : P × SymmetricExactJet E data.p => afterFirst a)
        (measurable_fst.comp measurable_snd) hafterFirst
      convert hwhole using 1
      funext qs
      simp only [halvingProgramAux, ExactJetProgram.bind]
      congr 1
      funext jetx
      by_cases hxy : (knownModelStep data qs.2.1 jetx).1.1 = qs.2.1.1
      · have hxy' : (knownModelStep data qs.2.1 jetx).1 = qs.2.1 :=
          Subtype.ext hxy
        simp [afterFirst, ExactJetProgram.actionPiecewise, earlySet, model,
          earlyProgram, halvingEarly, ExactJetProgram.bind, hxy']
      · have hxy' : ¬(knownModelStep data qs.2.1 jetx).1 = qs.2.1 :=
          fun h => hxy (congrArg Subtype.val h)
        simp [afterFirst, ExactJetProgram.actionPiecewise, earlySet, model,
          lateProgram, lateTail, halvingNextState, compactProjection,
          ExactJetProgram.bind, hxy, hxy']

end HalvingCPS

section HalvingCPSOutcome

variable (data : VIPublicData E) (mu : ℝ)

/-- Outcome-retaining CPS form of Halve.  In particular, a later operation may
measurably inspect every field of the returned `HalvingOutput`. -/
theorem halvingProgramAux_bind_isJointlyBorelOutcome
    {Q : Type v} {Output : Type w} [MeasurableSpace Q] [MeasurableSpace Output]
    (next : Q × HalvingOutput data → ExactJetProgram data.X
      (SymmetricExactJet E data.p) Output)
    (hnext : ExactJetProgram.IsJointlyBorelOutcome next)
    (remaining : ℕ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun qs : Q × HalvingBorelState data =>
        (halvingProgramAux data mu remaining qs.2.1 qs.2.2.1 qs.2.2.2).bind
          (fun out => next (qs.1, out))) := by
  induction remaining with
  | zero =>
      have hparam : Measurable (fun qs : Q × HalvingBorelState data =>
          (qs.1, halvingTerminal data qs.2)) :=
        measurable_fst.prodMk ((measurable_halvingTerminal data).comp measurable_snd)
      simpa [halvingProgramAux, halvingTerminal, ExactJetProgram.bind] using
        hnext.compParameter _ hparam
  | succ remaining ih =>
      let P := Q × HalvingBorelState data
      let A := P × SymmetricExactJet E data.p
      let model : A → data.X × E := fun a => knownModelStep data a.1.2.1 a.2
      have hmodel : Measurable model :=
        (measurable_knownModelStep_componentwise data).comp
          ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
            measurable_snd)
      let earlySet : Set A := {a | (model a).1 = a.1.2.1}
      have hearlySet : MeasurableSet earlySet :=
        measurableSet_eq_fun (measurable_fst.comp hmodel)
          (measurable_fst.comp (measurable_snd.comp measurable_fst))
      let earlyProgram : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) Output := fun a =>
        next (a.1.1, halvingEarly data (a.1.2, a.2))
      have hearlyProgram :
          ExactJetProgram.IsJointlyBorelOutcome earlyProgram :=
        hnext.compParameter
          (fun a : A => (a.1.1, halvingEarly data (a.1.2, a.2)))
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_halvingEarly data).comp
              ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      let lateTail : (A × SymmetricExactJet E data.p) →
          ExactJetProgram data.X (SymmetricExactJet E data.p) Output := fun a =>
        (halvingProgramAux data mu remaining
          (halvingNextState data ((a.1.1.2, a.1.2), a.2)).1
          (halvingNextState data ((a.1.1.2, a.1.2), a.2)).2.1
          (halvingNextState data ((a.1.1.2, a.1.2), a.2)).2.2).bind
            (fun out => next (a.1.1.1, out))
      have hlateTail : ExactJetProgram.IsJointlyBorelOutcome lateTail :=
        ih.compParameter
          (fun a : A × SymmetricExactJet E data.p =>
            (a.1.1.1, halvingNextState data ((a.1.1.2, a.1.2), a.2)))
          ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            ((measurable_halvingNextState data).comp
              (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
                (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
      let lateProgram : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) Output := fun a =>
        .query (model a).1 (fun jety => lateTail (a, jety))
      have hlateProgram : ExactJetProgram.IsJointlyBorelOutcome lateProgram :=
        ExactJetProgram.isJointlyBorelOutcome_query
          (fun a : A => (model a).1) lateTail
          (measurable_fst.comp hmodel) hlateTail
      let afterFirst : A → ExactJetProgram data.X
          (SymmetricExactJet E data.p) Output :=
        ExactJetProgram.actionPiecewise earlySet earlyProgram lateProgram
      have hafterFirst : ExactJetProgram.IsJointlyBorelOutcome afterFirst :=
        ExactJetProgram.isJointlyBorelOutcome_piecewise earlySet hearlySet
          earlyProgram lateProgram hearlyProgram hlateProgram
      have hwhole := ExactJetProgram.isJointlyBorelOutcome_query
        (fun qs : P => qs.2.1)
        (fun a : P × SymmetricExactJet E data.p => afterFirst a)
        (measurable_fst.comp measurable_snd) hafterFirst
      convert hwhole using 1
      funext qs
      simp only [halvingProgramAux, ExactJetProgram.bind]
      congr 1
      funext jetx
      by_cases hxy : (knownModelStep data qs.2.1 jetx).1.1 = qs.2.1.1
      · have hxy' : (knownModelStep data qs.2.1 jetx).1 = qs.2.1 :=
          Subtype.ext hxy
        simp [afterFirst, ExactJetProgram.actionPiecewise, earlySet, model,
          earlyProgram, halvingEarly, ExactJetProgram.bind, hxy']
      · have hxy' : ¬(knownModelStep data qs.2.1 jetx).1 = qs.2.1 :=
          fun h => hxy (congrArg Subtype.val h)
        simp [afterFirst, ExactJetProgram.actionPiecewise, earlySet, model,
          lateProgram, lateTail, halvingNextState, compactProjection,
          ExactJetProgram.bind, hxy, hxy']

end HalvingCPSOutcome

section CorrectionJoint

variable (data : VIPublicData E) (fallback : data.X)

/-- Joint form of the complete two-query correction rule.  The center is a
measurable parameter, which is needed after a preceding Halve call. -/
theorem correctionProgram_isJointlyBorelAction (delta : ℝ) :
    ExactJetProgram.IsJointlyBorelAction (certifiedCallOutput data fallback)
      (fun center : data.X => correctionProgram data center delta) := by
  classical
  let A := data.X × SymmetricExactJet E data.p
  let model : A → data.X × E := fun a => knownModelStep data a.1 a.2
  have hmodel : Measurable model := measurable_knownModelStep_componentwise data
  let B := A × SymmetricExactJet E data.p
  let point : B → data.X := fun b => (model b.1).1
  let normal : B → E := fun b => (model b.1).2
  let value : B → E := fun b => symmetricJetValue data b.2
  have hp : Measurable point := measurable_fst.comp hmodel |>.comp measurable_fst
  have hn : Measurable normal := measurable_snd.comp hmodel |>.comp measurable_fst
  have hv : Measurable value :=
    (measurable_symmetricJetValue_componentwise data).comp measurable_snd
  let normalGood : Set B := {b | normal b ∈ normalCone data.X (point b).1}
  have hnormalGood : MeasurableSet normalGood :=
    (isClosed_upperNormalConeGraph data.X).measurableSet.preimage
      ((measurable_subtype_coe.comp hp).prodMk hn)
  let residualGood (delta : ℝ) : Set B :=
    {b | ‖value b + normal b‖ ≤ delta}
  have hresidualGood (delta : ℝ) : MeasurableSet (residualGood delta) :=
    measurableSet_Iic.preimage ((hv.add hn).norm)
  let terminal (delta : ℝ) : B → ExactJetProgram data.X
      (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) := fun b =>
    let cert : EvaluatedNormalCertificate data := {
      point := point b, normal := normal b, value := value b }
    .halt (if cert.normal ∈ normalCone data.X cert.point.1 then
      if ‖cert.value + cert.normal‖ ≤ delta then some cert else none
    else none)
  have hterminal (delta : ℝ) :
      ExactJetProgram.IsJointlyBorelAction
        (certifiedCallOutput data fallback) (terminal delta) := by
    apply ExactJetProgram.isJointlyBorelAction_halt
    have hgood : MeasurableSet (normalGood ∩ residualGood delta) :=
      hnormalGood.inter (hresidualGood delta)
    have hout : Measurable (fun b : B =>
        if b ∈ normalGood ∩ residualGood delta then point b else fallback) :=
      Measurable.ite hgood hp measurable_const
    convert hout using 1
    funext b
    by_cases hnormal : normal b ∈ normalCone data.X (point b).1
    · by_cases hres : ‖value b + normal b‖ ≤ delta
      · simp [terminal, certifiedCallOutput, normalGood, residualGood,
          point, normal, value, hnormal, hres]
      · simp [terminal, certifiedCallOutput, normalGood, residualGood,
          point, normal, value, hnormal, hres]
    · simp [terminal, certifiedCallOutput, normalGood, residualGood,
        point, normal, value, hnormal]
  let afterFirst (delta : ℝ) : A → ExactJetProgram data.X
      (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) := fun a =>
    .query (model a).1 (fun jety => terminal delta (a, jety))
  have hafterFirst (delta : ℝ) :
      ExactJetProgram.IsJointlyBorelAction
        (certifiedCallOutput data fallback) (afterFirst delta) :=
    ExactJetProgram.isJointlyBorelAction_query _
      (fun a : A => (model a).1)
      (fun b : A × SymmetricExactJet E data.p => terminal delta b)
      (measurable_fst.comp hmodel) (hterminal delta)
  have hwhole := ExactJetProgram.isJointlyBorelAction_query
    (certifiedCallOutput data fallback)
    (fun center : data.X => center)
    (fun a : data.X × SymmetricExactJet E data.p => afterFirst delta a)
    measurable_id (hafterFirst delta)
  convert hwhole using 1
  funext center
  simp only [correctionProgram]
  congr 1
  funext jetx
  simp only [afterFirst, model]
  congr 1
  funext jety
  by_cases hnormal : (knownModelStep data center jetx).2 ∈
      normalCone data.X (knownModelStep data center jetx).1.1
  · by_cases hres : ‖symmetricJetValue data jety +
        (knownModelStep data center jetx).2‖ ≤ delta
    · simp [terminal, point, normal, value, model, hnormal, hres]
    · simp [terminal, point, normal, value, model, hnormal, hres]
  · simp [terminal, point, normal, value, model, hnormal]

end CorrectionJoint

section CorrectionOutcome

variable (data : VIPublicData E)

local instance upperCertificateMeasurableSpace_correction :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  upperEvaluatedNormalCertificateMeasurableSpace data

/-- The complete correction operation is jointly Borel in its center, while
retaining the returned evaluated certificate rather than merely its point. -/
theorem correctionProgram_isJointlyBorelOutcome (delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun center : data.X => correctionProgram data center delta) := by
  classical
  let A := data.X × SymmetricExactJet E data.p
  let model : A → data.X × E := fun a => knownModelStep data a.1 a.2
  have hmodel : Measurable model := measurable_knownModelStep_componentwise data
  let B := A × SymmetricExactJet E data.p
  let point : B → data.X := fun b => (model b.1).1
  let normal : B → E := fun b => (model b.1).2
  let value : B → E := fun b => symmetricJetValue data b.2
  have hp : Measurable point := measurable_fst.comp hmodel |>.comp measurable_fst
  have hn : Measurable normal := measurable_snd.comp hmodel |>.comp measurable_fst
  have hv : Measurable value :=
    (measurable_symmetricJetValue_componentwise data).comp measurable_snd
  let cert : B → EvaluatedNormalCertificate data := fun b =>
    { point := point b, normal := normal b, value := value b }
  have hcert : Measurable cert := by
    apply measurable_evaluatedNormalCertificate_mk data
    · rw [← upperFeasible_measurable_eq_normBorel data]
      exact hp
    · rw [← BorelSpace.measurable_eq]
      exact hn
    · rw [← BorelSpace.measurable_eq]
      exact hv
  let terminal : B → ExactJetProgram data.X
      (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) := fun b =>
    .halt (checkedEvaluatedNormalCertificate data delta (cert b))
  have hterminal : ExactJetProgram.IsJointlyBorelOutcome terminal := by
    apply ExactJetProgram.isJointlyBorelOutcome_halt
    exact (measurable_checkedEvaluatedNormalCertificate data delta).comp hcert
  let afterFirst : A → ExactJetProgram data.X
      (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) := fun a =>
    .query (model a).1 (fun jety => terminal (a, jety))
  have hafterFirst : ExactJetProgram.IsJointlyBorelOutcome afterFirst :=
    ExactJetProgram.isJointlyBorelOutcome_query
      (fun a : A => (model a).1)
      (fun b : A × SymmetricExactJet E data.p => terminal b)
      (measurable_fst.comp hmodel) hterminal
  have hwhole := ExactJetProgram.isJointlyBorelOutcome_query
    (fun center : data.X => center)
    (fun a : data.X × SymmetricExactJet E data.p => afterFirst a)
    measurable_id hafterFirst
  convert hwhole using 1
  funext center
  simp only [correctionProgram]
  congr 1
  funext jetx
  simp only [afterFirst, model]
  congr 1
  funext jety
  by_cases hnormal : (knownModelStep data center jetx).2 ∈
      normalCone data.X (knownModelStep data center jetx).1.1
  · by_cases hres : ‖symmetricJetValue data jety +
        (knownModelStep data center jetx).2‖ ≤ delta
    · simp [terminal, cert, checkedEvaluatedNormalCertificate, point, normal,
        value, model, hnormal, hres]
    · simp [terminal, cert, checkedEvaluatedNormalCertificate, point, normal,
        value, model, hnormal, hres]
  · simp [terminal, cert, checkedEvaluatedNormalCertificate, point, normal,
      value, model, hnormal]

end CorrectionOutcome

/-- Replacing the public start point does not change the canonical datum fed
to the total model selector. -/
@[simp] theorem canonicalModelData_withStart (data : VIPublicData E)
    (anchor : data.X) :
    canonicalModelData (data.withStart anchor) = canonicalModelData data := by
  rfl

/-- The executable total selector is stable under a change of the irrelevant
public anchor. -/
@[simp] theorem knownModelStep_withStart (data : VIPublicData E)
    (anchor x : data.X) (jet : SymmetricExactJet E data.p) :
    knownModelStep (data.withStart anchor) x jet = knownModelStep data x jet := by
  rfl

/-- Changing the public start point and transporting the returned certificate
back is operationally invisible to the two-query correction program. -/
theorem correctionProgram_fromWithStart_eq (data : VIPublicData E)
    (anchor center : data.X) (delta : ℝ) :
    (correctionProgram (data.withStart anchor) center delta).bind
        (fun cert => .halt (some (cert.fromWithStart data anchor))) =
      correctionProgram data center delta := by
  simp only [correctionProgram, ExactJetProgram.bind]
  congr 1
  funext jetx
  congr 1
  funext jety
  simp only [VIPublicData.withStart, knownModelStep, canonicalModelData,
    symmetricJetValue]
  split
  · split <;>
      simp [ExactJetProgram.bind, EvaluatedNormalCertificate.fromWithStart]
  · simp [ExactJetProgram.bind]

/-- Erase the irrelevant public-anchor index from a Halve result. -/
def HalvingOutput.fromWithStart (data : VIPublicData E) (anchor : data.X)
    (out : HalvingOutput (data.withStart anchor)) : HalvingOutput data where
  point := out.point
  early := out.early
  normal := out.normal
  value := out.value

/-- A Halve execution is independent of the public start point, after the
phantom anchor index on its output has been erased. -/
theorem halvingProgramAux_fromWithStart_eq (data : VIPublicData E)
    (anchor : data.X) (mu : ℝ) (remaining : ℕ) (x : data.X)
    (weighted : E) (Lambda : ℝ) :
    (halvingProgramAux (data.withStart anchor) mu remaining x weighted Lambda).bind
        (fun out => .halt (some (HalvingOutput.fromWithStart data anchor out))) =
      halvingProgramAux data mu remaining x weighted Lambda := by
  induction remaining generalizing x weighted Lambda with
  | zero =>
      simp [halvingProgramAux, ExactJetProgram.bind, HalvingOutput.fromWithStart,
        VIPublicData.withStart]
  | succ remaining ih =>
      simp only [halvingProgramAux, ExactJetProgram.bind]
      congr 1
      funext jetx
      change SymmetricExactJet E data.p at jetx
      have hmodel : knownModelStep (data.withStart anchor) x jetx =
          knownModelStep data x jetx := knownModelStep_withStart data anchor x jetx
      by_cases hs : (knownModelStep (data.withStart anchor) x jetx).1.1 = x.1
      · have hb : (knownModelStep data x jetx).1.1 = x.1 := by
          simpa only [hmodel] using hs
        simp only [hs, hb, ↓reduceDIte, ExactJetProgram.bind]
        congr 2
      · have hb : ¬(knownModelStep data x jetx).1.1 = x.1 := by
          simpa only [hmodel] using hs
        simp only [hs, hb, ↓reduceDIte, ExactJetProgram.bind]
        have hp := congrArg Prod.fst hmodel
        nth_rw 1 [hp]
        congr 1
        funext jety
        change SymmetricExactJet E data.p at jety
        let shifted := data.withStart anchor
        let lambda := 1 / (tensorBetaCoefficient shifted.p * shifted.Lp *
          ‖(knownModelStep shifted x jetx).1.1 - x.1‖ ^ (shifted.p - 1))
        let xp := compactConvexProjection shifted.X shifted.X_nonempty
          shifted.X_compact shifted.X_convex
          (x.1 - lambda • symmetricJetValue shifted jety)
        have hi := ih (x := ⟨xp, compactConvexProjection_mem shifted.X
            shifted.X_nonempty shifted.X_compact shifted.X_convex _⟩)
          (weighted := weighted + lambda • (knownModelStep shifted x jetx).1.1)
          (Lambda := Lambda + lambda)
        let lambdaB := 1 / (tensorBetaCoefficient data.p * data.Lp *
          ‖(knownModelStep data x jetx).1.1 - x.1‖ ^ (data.p - 1))
        have hfirst : (knownModelStep shifted x jetx).1.1 =
            (knownModelStep data x jetx).1.1 :=
          congrArg (fun q : data.X × E => q.1.1) hmodel
        have hlambda : lambda = lambdaB := by
          dsimp [lambda, lambdaB, shifted]
          rw [hfirst]
          rfl
        have hvalue : symmetricJetValue shifted jety =
            symmetricJetValue data jety := by rfl
        let xpB := compactConvexProjection data.X data.X_nonempty data.X_compact
          data.X_convex (x.1 - lambdaB • symmetricJetValue data jety)
        have hxp : xp = xpB := by
          change compactConvexProjection shifted.X shifted.X_nonempty
              shifted.X_compact shifted.X_convex
                (x.1 - lambda • symmetricJetValue shifted jety) =
            compactConvexProjection data.X data.X_nonempty data.X_compact
              data.X_convex (x.1 - lambdaB • symmetricJetValue data jety)
          rw [hlambda, hvalue]
          rfl
        have hcenter :
            (⟨xp, compactConvexProjection_mem shifted.X shifted.X_nonempty
              shifted.X_compact shifted.X_convex _⟩ : data.X) =
            ⟨xpB, compactConvexProjection_mem data.X data.X_nonempty
              data.X_compact data.X_convex _⟩ := Subtype.ext hxp
        have hweighted :
            weighted + lambda • (knownModelStep shifted x jetx).1.1 =
              weighted + lambdaB • (knownModelStep data x jetx).1.1 := by
          rw [hlambda]
          exact congrArg (fun z : data.X => weighted + lambdaB • z.1) hp
        have hLambda : Lambda + lambda = Lambda + lambdaB := by rw [hlambda]
        calc
          _ = halvingProgramAux data mu remaining
              ⟨xp, compactConvexProjection_mem shifted.X shifted.X_nonempty
                shifted.X_compact shifted.X_convex _⟩
              (weighted + lambda • (knownModelStep shifted x jetx).1.1)
              (Lambda + lambda) := hi
          _ = _ := by rw [hcenter, hweighted, hLambda]

/-- Public Halve call form of `halvingProgramAux_fromWithStart_eq`. -/
theorem halvingProgram_fromWithStart_eq (data : VIPublicData E)
    (anchor center : data.X) (mu R : ℝ) :
    (halvingProgram (data.withStart anchor) center mu R).bind
        (fun out => .halt (some (HalvingOutput.fromWithStart data anchor out))) =
      halvingProgram data center mu R := by
  simpa [halvingProgram, VIPublicData.withStart] using
    halvingProgramAux_fromWithStart_eq data anchor mu
      (halvingIterationCount data.p data.Lp R mu) center 0 0

section BaseTrial

variable (data : VIPublicData E) (fallback : data.X)

theorem measurable_halvingOutput_point :
    Measurable (HalvingOutput.point : HalvingOutput data → E) := by
  exact measurable_fst.comp
    (comap_measurable (HalvingOutput.coordinates data))

/-- Total feasible interpretation of the ambient point saved by Halve.  The
fallback is used only on counterfactual invalid transcripts. -/
def feasibleHalvingPoint (out : HalvingOutput data) : data.X := by
  classical
  exact if h : out.point ∈ data.X then ⟨out.point, h⟩ else fallback

theorem measurable_feasibleHalvingPoint :
    Measurable (feasibleHalvingPoint data fallback) := by
  classical
  have hset : MeasurableSet {out : HalvingOutput data | out.point ∈ data.X} :=
    data.X_compact.isClosed.measurableSet.preimage
      (measurable_halvingOutput_point data)
  unfold feasibleHalvingPoint
  refine Measurable.dite
    (s := {out : HalvingOutput data | out.point ∈ data.X})
    (f := fun out => (⟨out.1.point, out.2⟩ : data.X))
    (g := fun _ => fallback) ?_ measurable_const hset
  exact ((measurable_halvingOutput_point data).comp measurable_subtype_coe).subtype_mk

/-- A complete BaseTrial has a Borel replay action jointly in its center;
the radius, accuracy, and finite number of Halve calls are public constants. -/
theorem baseTrialProgram_isJointlyBorelAction
    (mu delta : ℝ) (halvings : ℕ) (R : ℝ) :
    ExactJetProgram.IsJointlyBorelAction (certifiedCallOutput data fallback)
      (fun center : data.X =>
        baseTrialProgram data mu delta halvings center R) := by
  induction halvings generalizing R with
  | zero =>
      simpa [baseTrialProgram] using
        correctionProgram_isJointlyBorelAction data fallback delta
  | succ halvings ih =>
      let P := Unit × HalvingOutput data
      let good : Set P := {qout | qout.2.point ∈ data.X}
      have hgood : MeasurableSet good := by
        exact data.X_compact.isClosed.measurableSet.preimage
          ((measurable_halvingOutput_point data).comp measurable_snd)
      let first : P → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) := fun qout =>
        baseTrialProgram data mu delta halvings
          (feasibleHalvingPoint data fallback qout.2) (R / 2)
      have hfirst : ExactJetProgram.IsJointlyBorelAction
          (certifiedCallOutput data fallback) first := by
        exact (ih (R / 2)).compParameter
          (fun qout : P => feasibleHalvingPoint data fallback qout.2)
          ((measurable_feasibleHalvingPoint data fallback).comp measurable_snd)
      let second : P → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) :=
        fun _ => .halt none
      have hsecond : ExactJetProgram.IsJointlyBorelAction
          (certifiedCallOutput data fallback) second := by
        exact ExactJetProgram.isJointlyBorelAction_halt _
          (fun _ : P => none) measurable_const
      let next : P → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) :=
        ExactJetProgram.actionPiecewise good first second
      have hnext : ExactJetProgram.IsJointlyBorelAction
          (certifiedCallOutput data fallback) next :=
        ExactJetProgram.isJointlyBorelAction_piecewise _ good hgood
          first second hfirst hsecond
      have hcps := halvingProgramAux_bind_isJointlyBorelAction data mu
        (certifiedCallOutput data fallback) next hnext
        (halvingIterationCount data.p data.Lp R mu)
      have hfixed := hcps.compParameter
        (fun center : data.X => ((), center, 0, 0))
        (measurable_const.prodMk
          (measurable_id.prodMk (measurable_const.prodMk measurable_const)))
      convert hfixed using 1
      funext center
      simp only [baseTrialProgram, halvingProgram]
      congr 1
      funext out
      by_cases hmem : out.point ∈ data.X
      · have heq : feasibleHalvingPoint data fallback out = ⟨out.point, hmem⟩ := by
          simp [feasibleHalvingPoint, hmem]
        simp [next, ExactJetProgram.actionPiecewise, good, first, hmem, heq]
      · simp [next, ExactJetProgram.actionPiecewise, good, second, hmem]

local instance upperCertificateMeasurableSpace_baseTrial :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  upperEvaluatedNormalCertificateMeasurableSpace data

/-- Outcome-retaining version of the complete finite base trial. -/
theorem baseTrialProgram_isJointlyBorelOutcome
    (fallback : data.X) (mu delta : ℝ) (halvings : ℕ) (R : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun center : data.X => baseTrialProgram data mu delta halvings center R) := by
  induction halvings generalizing R with
  | zero =>
      simpa [baseTrialProgram] using
        correctionProgram_isJointlyBorelOutcome data delta
  | succ halvings ih =>
      let P := Unit × HalvingOutput data
      let good : Set P := {qout | qout.2.point ∈ data.X}
      have hgood : MeasurableSet good :=
        data.X_compact.isClosed.measurableSet.preimage
          ((measurable_halvingOutput_point data).comp measurable_snd)
      let first : P → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) := fun qout =>
        baseTrialProgram data mu delta halvings
          (feasibleHalvingPoint data fallback qout.2) (R / 2)
      have hfirst : ExactJetProgram.IsJointlyBorelOutcome first :=
        (ih (R / 2)).compParameter
          (fun qout : P => feasibleHalvingPoint data fallback qout.2)
          ((measurable_feasibleHalvingPoint data fallback).comp measurable_snd)
      let second : P → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) :=
        fun _ => .halt none
      have hsecond : ExactJetProgram.IsJointlyBorelOutcome second :=
        ExactJetProgram.isJointlyBorelOutcome_halt
          (fun _ : P => none) measurable_const
      let next : P → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) :=
        ExactJetProgram.actionPiecewise good first second
      have hnext : ExactJetProgram.IsJointlyBorelOutcome next :=
        ExactJetProgram.isJointlyBorelOutcome_piecewise good hgood
          first second hfirst hsecond
      have hcps := halvingProgramAux_bind_isJointlyBorelOutcome data mu
        next hnext (halvingIterationCount data.p data.Lp R mu)
      have hfixed := hcps.compParameter
        (fun center : data.X => ((), center, 0, 0))
        (measurable_const.prodMk
          (measurable_id.prodMk (measurable_const.prodMk measurable_const)))
      convert hfixed using 1
      funext center
      simp only [baseTrialProgram, halvingProgram]
      congr 1
      funext out
      by_cases hmem : out.point ∈ data.X
      · have heq : feasibleHalvingPoint data fallback out = ⟨out.point, hmem⟩ := by
          simp [feasibleHalvingPoint, hmem]
        simp [next, ExactJetProgram.actionPiecewise, good, first, hmem, heq]
      · simp [next, ExactJetProgram.actionPiecewise, good, second, hmem]

theorem baseTrialProgram_isBorelOutcome
    (fallback : data.X) (mu delta : ℝ) (halvings : ℕ)
    (center : data.X) (R : ℝ) :
    ExactJetProgram.IsBorelOutcome
      (baseTrialProgram data mu delta halvings center R) :=
  (baseTrialProgram_isJointlyBorelOutcome data fallback
    mu delta halvings R).fixed center

/-- A complete base trial is independent of the public start point after its
successful certificate is transported back to the fixed public datum. -/
theorem baseTrialProgram_fromWithStart_eq (data : VIPublicData E)
    (anchor : data.X) (mu delta : ℝ) (halvings : ℕ)
    (center : data.X) (R : ℝ) :
    (baseTrialProgram (data.withStart anchor) mu delta halvings center R).bind
        (fun cert => .halt (some (cert.fromWithStart data anchor))) =
      baseTrialProgram data mu delta halvings center R := by
  classical
  induction halvings generalizing center R with
  | zero => exact correctionProgram_fromWithStart_eq data anchor center delta
  | succ halvings ih =>
      simp only [baseTrialProgram]
      rw [ExactJetProgram.bind_assoc_eq]
      let pS := halvingProgram (data.withStart anchor) center mu R
      let transport := fun out : HalvingOutput (data.withStart anchor) =>
        HalvingOutput.fromWithStart data anchor out
      let nextB := fun out : HalvingOutput data =>
        if hmem : out.point ∈ data.X then
          baseTrialProgram data mu delta halvings ⟨out.point, hmem⟩ (R / 2)
        else .halt none
      have hhalving : pS.bind (fun out => .halt (some (transport out))) =
          halvingProgram data center mu R :=
        halvingProgram_fromWithStart_eq data anchor center mu R
      calc
        _ = pS.bind (fun out => nextB (transport out)) := by
          congr 1
          funext out
          by_cases hmem : out.point ∈ data.X
          · simpa [VIPublicData.withStart, nextB, transport,
              HalvingOutput.fromWithStart, hmem, ExactJetProgram.bind] using
              ih ⟨out.point, hmem⟩ (R / 2)
          · simp [VIPublicData.withStart, nextB, transport,
              HalvingOutput.fromWithStart, hmem, ExactJetProgram.bind]
        _ = (pS.bind (fun out => .halt (some (transport out)))).bind nextB := by
          rw [ExactJetProgram.bind_assoc_eq]
          rfl
        _ = _ := by
          rw [hhalving]
          rfl

/-- BaseTrial's public cap is independent of the public start point. -/
theorem baseTrialCap_withStart (data : VIPublicData E) (anchor : data.X)
    (mu : ℝ) (n : ℕ) (R : ℝ) :
    baseTrialCap (data.withStart anchor) mu n R = baseTrialCap data mu n R := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
      simp only [baseTrialCap]
      congr 1
      exact ih (R / 2)

/-- The complete adaptive finite radius search is likewise independent of the
public start point after successful certificates are transported back. -/
theorem adaptiveBaseProgramFrom_fromWithStart_eq (data : VIPublicData E)
    (anchor : data.X) (mu delta : ℝ) (remaining j : ℕ)
    (center : data.X) :
    (adaptiveBaseProgramFrom (data.withStart anchor) mu delta center remaining j).bind
        (fun cert => .halt (some (cert.fromWithStart data anchor))) =
      adaptiveBaseProgramFrom data mu delta center remaining j := by
  classical
  induction remaining generalizing j with
  | zero =>
      simp only [adaptiveBaseProgramFrom, scheduledBaseTrialCall, baseTrialCall]
      rw [← ExactJetProgram.locallyCapped_bind_halt_some]
      rw [baseTrialProgram_fromWithStart_eq]
      congr 1
      exact baseTrialCap_withStart data anchor mu _ _
  | succ remaining ih =>
      simp only [adaptiveBaseProgramFrom]
      rw [ExactJetProgram.orElse_bind_halt_some]
      simp only [scheduledBaseTrialCall, baseTrialCall]
      rw [← ExactJetProgram.locallyCapped_bind_halt_some]
      rw [baseTrialProgram_fromWithStart_eq]
      rw [ih (j + 1)]
      congr 2
      exact baseTrialCap_withStart data anchor mu _ _

/-- The uncapped program stored in a scheduled child trial is jointly Borel
in the public center for fixed numerical inputs. -/
theorem scheduledBaseTrialProgram_isJointlyBorelOutcome
    (mu delta R : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      (scheduledBaseTrialCall data mu delta center R).program) := by
  let fallback : data.X := ⟨Classical.choose data.X_nonempty,
    Classical.choose_spec data.X_nonempty⟩
  simpa [scheduledBaseTrialCall, baseTrialCall] using
    (baseTrialProgram_isJointlyBorelOutcome data fallback mu delta
      (baseHalvingCount data R delta) R)

/-- A scheduled child trial, including its installed local cap, is jointly
Borel in the public center for fixed numerical inputs. -/
theorem scheduledBaseTrialProgram_locallyCapped_isJointlyBorelOutcome
    (mu delta R : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      let call := scheduledBaseTrialCall data mu delta center R
      call.program.locallyCapped call.cap) := by
  let fallback : data.X := ⟨Classical.choose data.X_nonempty,
    Classical.choose_spec data.X_nonempty⟩
  have hbase := baseTrialProgram_isJointlyBorelOutcome data fallback mu delta
    (baseHalvingCount data R delta) R
  have hcapped := hbase.locallyCappedOutcome
    (baseTrialCap data mu (baseHalvingCount data R delta) R)
  simpa [scheduledBaseTrialCall, baseTrialCall] using hcapped

/-- The whole finite adaptive radius search is jointly Borel in its original
center.  Explicit failure of one locally capped child is the only branch that
continues to the next public radius. -/
theorem adaptiveBaseProgramFrom_isJointlyBorelOutcome
    (mu delta : ℝ) (remaining j : ℕ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      adaptiveBaseProgramFrom data mu delta center remaining j) := by
  let dummy : data.X := ⟨Classical.choose data.X_nonempty,
    Classical.choose_spec data.X_nonempty⟩
  induction remaining generalizing j with
  | zero =>
      simpa [adaptiveBaseProgramFrom] using
        scheduledBaseTrialProgram_locallyCapped_isJointlyBorelOutcome data
          mu delta (adaptiveGuessRadius data mu j)
  | succ remaining ih =>
      let R := adaptiveGuessRadius data mu j
      have hfirst := scheduledBaseTrialProgram_isJointlyBorelOutcome data
        mu delta R
      have hfallback := ih (j + 1)
      have h := hfirst.orElse_locallyCapped hfallback dummy
        (baseTrialCap data mu (baseHalvingCount data R delta) R)
      simpa [adaptiveBaseProgramFrom, scheduledBaseTrialCall, baseTrialCall, R]
        using h

/-- Joint Borel outcome for the concrete adaptive base call. -/
theorem adaptiveBaseCall_isJointlyBorelOutcome (mu delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      (adaptiveBaseCall data center mu delta).program) := by
  simpa [adaptiveBaseCall] using
    adaptiveBaseProgramFrom_isJointlyBorelOutcome data mu delta
      (adaptiveGuessCount data mu) 0

/-- The advertised adaptive cap depends only on public numerical data, not on
the center at which the call is installed. -/
theorem adaptiveBaseCapFrom_center_eq (mu delta : ℝ)
    (center₁ center₂ : data.X) (remaining j : ℕ) :
    adaptiveBaseCapFrom data mu delta center₁ remaining j =
      adaptiveBaseCapFrom data mu delta center₂ remaining j := by
  induction remaining generalizing j with
  | zero => rfl
  | succ remaining ih =>
      simp only [adaptiveBaseCapFrom]
      congr 1
      exact ih (j + 1)

/-- The adaptive sum of installed child caps is stable under changing the
public start point. -/
theorem adaptiveBaseCapFrom_withStart (data : VIPublicData E)
    (anchor : data.X) (mu delta : ℝ) (center : data.X)
    (remaining j : ℕ) :
    adaptiveBaseCapFrom (data.withStart anchor) mu delta center remaining j =
      adaptiveBaseCapFrom data mu delta center remaining j := by
  induction remaining generalizing j with
  | zero =>
      simp only [adaptiveBaseCapFrom, scheduledBaseTrialCall, baseTrialCall]
      exact baseTrialCap_withStart data anchor mu _ _
  | succ remaining ih =>
      simp only [adaptiveBaseCapFrom, scheduledBaseTrialCall, baseTrialCall]
      congr 1
      · exact baseTrialCap_withStart data anchor mu _ _
      · exact ih (j + 1)

/-- Call-level anchor transport for the concrete adaptive base solver. -/
theorem adaptiveBaseCall_fromWithStart_eq (data : VIPublicData E)
    (anchor center : data.X) (mu delta : ℝ) :
    (adaptiveBaseCall (data.withStart anchor) center mu delta).fromWithStart
        data anchor = adaptiveBaseCall data center mu delta := by
  unfold CappedExactJetCall.fromWithStart adaptiveBaseCall
  congr 1
  · exact adaptiveBaseCapFrom_withStart data anchor mu delta center _ 0
  · have h := adaptiveBaseProgramFrom_fromWithStart_eq data anchor mu delta
        (adaptiveGuessCount (data.withStart anchor) mu) 0 center
    have hc : adaptiveGuessCount (data.withStart anchor) mu =
        adaptiveGuessCount data mu := by rfl
    rw [hc] at h
    exact h

/-- Joint Borel outcome for the actual installed adaptive base call, including
its public hard cap. -/
theorem adaptiveBaseCall_installed_isJointlyBorelOutcome
    (fallback : data.X) (mu delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome (fun center : data.X =>
      let call := adaptiveBaseCall data center mu delta
      call.installedProgram data) := by
  have h := (adaptiveBaseCall_isJointlyBorelOutcome data mu delta).locallyCappedOutcome
    (adaptiveBaseCapFrom data mu delta fallback (adaptiveGuessCount data mu) 0)
  have heq : (fun center : data.X =>
      (adaptiveBaseCall data center mu delta).installedProgram data) =
      (fun center : data.X =>
        (adaptiveBaseCall data center mu delta).program.locallyCapped
          (adaptiveBaseCapFrom data mu delta fallback
            (adaptiveGuessCount data mu) 0)) := by
    funext center
    simp only [CappedExactJetCall.installedProgram, adaptiveBaseCall]
    rw [adaptiveBaseCapFrom_center_eq data mu delta center fallback]
  rw [heq]
  exact h

/-- Fixed-center Borel action for the installed capped BaseTrial call. -/
theorem baseTrialCall_isBorel (mu delta : ℝ) (halvings : ℕ)
    (center : data.X) (R : ℝ) :
    (baseTrialCall data mu delta halvings center R).IsBorel data fallback := by
  intro n
  have hprogram := (baseTrialProgram_isJointlyBorelAction data fallback
    mu delta halvings R).fixed center
  exact hprogram.locallyCappedAction
    (baseTrialCap data mu halvings R) n.1 (Nat.lt_succ_iff.mp n.2)

end BaseTrial

/-- Family-level Borel invariant required by the upper hierarchy compiler. -/
theorem baseStrongCertifiedFamily_hasJointBorelOutcome (p : ℕ) :
    (baseStrongCertifiedFamily p).HasJointBorelOutcome := by
  intro E _ _ _ _ _ data hp mu delta
  simpa [baseStrongCertifiedFamily, StrongSolverFamily.atData,
    baseStrongSolver] using adaptiveBaseCall_isJointlyBorelOutcome data mu delta

/-- The concrete certified base solver satisfies the hierarchy's strongest
operational Borel invariant: its installed cap is included, and measurability
is uniform in both a changed public anchor and the solve center. -/
theorem baseStrongCertifiedFamily_hasJointBorelCappedOutcome (p : ℕ) :
    (baseStrongCertifiedFamily p).HasJointBorelCappedOutcome := by
  constructor
  · intro E _ _ _ _ _ data hp mu delta
    letI : MeasurableSpace (EvaluatedNormalCertificate data) :=
      upperEvaluatedNormalCertificateMeasurableSpace data
    let fallback : data.X := ⟨Classical.choose data.X_nonempty,
      Classical.choose_spec data.X_nonempty⟩
    simpa [baseStrongCertifiedFamily, StrongSolverFamily.atData,
      baseStrongSolver] using
        adaptiveBaseCall_installed_isJointlyBorelOutcome data fallback mu delta
  · intro E _ _ _ _ _ data hp mu delta
    letI : MeasurableSpace (EvaluatedNormalCertificate data) :=
      upperEvaluatedNormalCertificateMeasurableSpace data
    let fallback : data.X := ⟨Classical.choose data.X_nonempty,
      Classical.choose_spec data.X_nonempty⟩
    have h := (adaptiveBaseCall_installed_isJointlyBorelOutcome
      data fallback mu delta).compParameter
        (fun state : data.X × data.X => state.2) measurable_snd
    have heq : (fun state : data.X × data.X =>
        let shifted := data.withStart state.1
        let call := adaptiveBaseCall shifted state.2 mu delta
        call.anchoredInstalledProgram data state.1) =
        (fun state : data.X × data.X =>
          (adaptiveBaseCall data state.2 mu delta).installedProgram data) := by
      funext state
      simp only [CappedExactJetCall.anchoredInstalledProgram]
      rw [adaptiveBaseCall_fromWithStart_eq]
    have hanchor : ExactJetProgram.IsJointlyBorelOutcome
        (fun state : data.X × data.X =>
          let shifted := data.withStart state.1
          let call := adaptiveBaseCall shifted state.2 mu delta
          call.anchoredInstalledProgram data state.1) := by
      rw [heq]
      exact h
    simpa [baseStrongCertifiedFamily, StrongSolverFamily.atData,
      baseStrongSolver] using hanchor

end

end VIReference.Pilot
