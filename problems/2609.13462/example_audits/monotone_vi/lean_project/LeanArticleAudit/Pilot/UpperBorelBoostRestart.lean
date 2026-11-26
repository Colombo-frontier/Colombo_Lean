import LeanArticleAudit.Pilot.UpperBorelCallOutcome
import LeanArticleAudit.Pilot.UpperBorelHalving
import LeanArticleAudit.Pilot.UpperBorelBase
import LeanArticleAudit.Pilot.UpperBoostTransformation
import LeanArticleAudit.Pilot.UpperRestartClaim

/-!
# Borel preservation for boost and certified restart

Generic finite-transcript composition rules and their concrete applications
to the upper boost/restart programs.
-/

open Set MeasureTheory

namespace LeanArticleAudit.Pilot

noncomputable section

universe u v w x y

/-! ### Measurable dependent case splits -/

theorem measurable_sum_cases
    {S : Type u} {A : Type v} {B : Type w} {C : Type x}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (selector : S → A ⊕ B) (hselector : Measurable selector)
    (left : S × A → C) (hleft : Measurable left)
    (right : S × B → C) (hright : Measurable right) :
    Measurable (fun s => selector s |>.elim
      (fun a => left (s, a)) (fun b => right (s, b))) := by
  have hdistrib : Measurable (fun s =>
      Equiv.prodSumDistrib S A B (s, selector s)) :=
    (MeasurableEquiv.prodSumDistrib S A B).measurable.comp
      (measurable_id.prodMk hselector)
  have h := (hleft.sumElim hright).comp hdistrib
  convert h using 1
  funext s
  cases hselectorValue : selector s <;>
    simp [hselectorValue]

theorem measurable_option_cases
    {S : Type u} {A : Type v} {C : Type w}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace C]
    (selector : S → Option A) (hselector : Measurable selector)
    (noneCase : S → C) (hnone : Measurable noneCase)
    (someCase : S × A → C) (hsome : Measurable someCase) :
    Measurable (fun s => (selector s).elim (noneCase s)
      (fun a => someCase (s, a))) := by
  have hsum : Measurable (fun s =>
      (Equiv.optionEquivSumPUnit A) (selector s)) :=
    measurable_optionEquivSumPUnit.comp hselector
  have h := measurable_sum_cases _ hsum someCase hsome
    (fun z : S × PUnit => noneCase z.1) (hnone.comp measurable_fst)
  convert h using 1
  funext s
  cases selector s <;> rfl

namespace ExactJetProgram

variable {X : Type u} {Answer : Type v} {Output : Type w}

/-! ### Answer transformations -/

theorem IsJointlyBorelOutcome.mapAnswers
    {Answer₁ : Type y} {Answer₂ : Type v}
    [MeasurableSpace X] [MeasurableSpace Answer₁]
    [MeasurableSpace Answer₂] [MeasurableSpace Output]
    [Inhabited X] [Inhabited Answer₂]
    {P : Type (max x v)} [MeasurableSpace P]
    {program : P → ExactJetProgram X Answer₂ Output}
    (hprogram : IsJointlyBorelOutcome program)
    (transform : X → Answer₁ → Answer₂)
    (htransform : Measurable (fun pair : X × Answer₁ =>
      transform pair.1 pair.2)) :
    IsJointlyBorelOutcome (fun parameter =>
      (program parameter).mapAnswers transform) := by
  intro n
  induction n generalizing P with
  | zero =>
      have h := hprogram 0
      have heq : (fun z : P × (Fin 0 → X × Answer₁) =>
          replayOutcomeAction ((program z.1).mapAnswers transform) z.2) =
          (fun z : P × (Fin 0 → X × Answer₂) =>
            replayOutcomeAction (program z.1) z.2) ∘
            (fun z => (z.1, fun i : Fin 0 => Fin.elim0 i)) := by
        funext z
        change replayOutcomeAction ((program z.1).mapAnswers transform) z.2 =
          replayOutcomeAction (program z.1)
            (fun i : Fin 0 => Fin.elim0 i)
        cases hroot : program z.1 <;>
          simp [ExactJetProgram.mapAnswers, replayOutcomeAction,
            residualAfterHistory, residualAfterAnswers]
      rw [heq]
      exact h.comp (measurable_fst.prodMk measurable_const)
  | succ n ih =>
      let S := P × (Fin (n + 1) → X × Answer₁)
      let emptyHistory : Fin 0 → X × Answer₂ := fun i => Fin.elim0 i
      let root : S → Sum (Option Output) X := fun z =>
        replayOutcomeAction (program z.1) emptyHistory
      have hroot : Measurable root := by
        exact (hprogram 0).comp (measurable_fst.prodMk measurable_const)
      let transformedAnswer : S → Answer₂ := fun z =>
        (root z).elim (fun _ => default)
          (fun point => transform point (z.2 0).2)
      have htransformedAnswer : Measurable transformedAnswer := by
        exact measurable_sum_cases root hroot
          (fun _ : S × Option Output => (default : Answer₂)) measurable_const
          (fun q : S × X => transform q.2 (q.1.2 0).2)
          (htransform.comp (measurable_snd.prodMk
            (measurable_snd.comp
              ((measurable_pi_apply (0 : Fin (n + 1))).comp
                (measurable_snd.comp measurable_fst)))))
      let tailHistory : S → (Fin n → X × Answer₁) := fun z i => z.2 i.succ
      have htailHistory : Measurable tailHistory := by
        rw [measurable_pi_iff]
        intro i
        change Measurable (fun z : P × (Fin (n + 1) → X × Answer₁) =>
          z.2 i.succ)
        fun_prop
      let residualFamily : P × Answer₂ →
          ExactJetProgram X Answer₂ Output := fun parameter =>
        ExactJetProgram.afterFirstAnswer (program parameter.1) parameter.2
      have hresidualFamily : IsJointlyBorelOutcome residualFamily :=
        hprogram.afterFirstAnswer default
      have hmappedResidual : Measurable (fun z :
          (P × Answer₂) × (Fin n → X × Answer₁) =>
          replayOutcomeAction
            ((residualFamily z.1).mapAnswers transform) z.2) :=
        ih hresidualFamily
      let tailOutcome : S → Sum (Option Output) X := fun z =>
        replayOutcomeAction
          ((residualFamily (z.1, transformedAnswer z)).mapAnswers transform)
          (tailHistory z)
      have htailOutcome : Measurable tailOutcome := by
        exact hmappedResidual.comp
          ((measurable_fst.prodMk htransformedAnswer).prodMk htailHistory)
      have hcases : Measurable (fun z : S =>
          (root z).elim Sum.inl (fun _ => tailOutcome z)) := by
        exact measurable_sum_cases root hroot
          (fun q : S × Option Output => Sum.inl q.2)
          (measurable_inl.comp measurable_snd)
          (fun q : S × X => tailOutcome q.1)
          (htailOutcome.comp measurable_fst)
      convert hcases using 1
      funext z
      cases hprogramRoot : program z.1 with
      | halt result =>
          have hrootValue : root z = Sum.inl result := by
            simp [root, emptyHistory, hprogramRoot, replayOutcomeAction,
              residualAfterHistory, residualAfterAnswers]
          rw [hrootValue]
          change replayOutcomeAction ((program z.1).mapAnswers transform) z.2 = _
          rw [hprogramRoot]
          change replayOutcomeAction (.halt result) z.2 = Sum.inl result
          simp [replayOutcomeAction, residualAfterHistory,
            residualAfterAnswers]
      | query point next =>
          have hrootValue : root z = Sum.inr point := by
            simp [root, emptyHistory, hprogramRoot, replayOutcomeAction,
              residualAfterHistory, residualAfterAnswers]
          have hanswer : transformedAnswer z =
              transform point (z.2 0).2 := by
            simp [transformedAnswer, hrootValue]
          rw [hrootValue]
          unfold tailOutcome residualFamily tailHistory
          rw [hanswer]
          change replayOutcomeAction ((program z.1).mapAnswers transform) z.2 = _
          rw [hprogramRoot]
          change replayOutcomeAction
              (.query point (fun answer₁ =>
                (next (transform point answer₁)).mapAnswers transform)) z.2 =
            replayOutcomeAction
              ((next (transform point (z.2 0).2)).mapAnswers transform)
              (fun i => z.2 i.succ)
          exact replayOutcomeAction_query_succ point
            (fun answer₁ => (next (transform point answer₁)).mapAnswers
              transform) z.2

/-- Parameter-dependent answer compilation.  This is the form needed when a
regularization center is part of a measurable outer state. -/
theorem IsJointlyBorelOutcome.mapAnswersWithParameter
    {X Answer₁ Answer₂ Output P : Type u}
    [MeasurableSpace X] [MeasurableSpace Answer₁]
    [MeasurableSpace Answer₂] [MeasurableSpace Output]
    [MeasurableSpace P] [Inhabited X] [Inhabited Answer₂]
    {program : P → ExactJetProgram X Answer₂ Output}
    (hprogram : IsJointlyBorelOutcome program)
    (transform : P × (X × Answer₁) → Answer₂)
    (htransform : Measurable transform) :
    IsJointlyBorelOutcome (fun parameter =>
      (program parameter).mapAnswers
        (fun point answer => transform (parameter, point, answer))) := by
  intro n
  induction n generalizing P with
  | zero =>
      have h := hprogram 0
      have heq : (fun z : P × (Fin 0 → X × Answer₁) =>
          replayOutcomeAction
            ((program z.1).mapAnswers
              (fun point answer => transform (z.1, point, answer))) z.2) =
          (fun z : P × (Fin 0 → X × Answer₂) =>
            replayOutcomeAction (program z.1) z.2) ∘
            (fun z => (z.1, fun i : Fin 0 => Fin.elim0 i)) := by
        funext z
        change replayOutcomeAction
            ((program z.1).mapAnswers
              (fun point answer => transform (z.1, point, answer))) z.2 =
          replayOutcomeAction (program z.1) (fun i : Fin 0 => Fin.elim0 i)
        cases hroot : program z.1 <;>
          simp [ExactJetProgram.mapAnswers, replayOutcomeAction,
            residualAfterHistory, residualAfterAnswers]
      rw [heq]
      exact h.comp (measurable_fst.prodMk measurable_const)
  | succ n ih =>
      let S := P × (Fin (n + 1) → X × Answer₁)
      let emptyHistory : Fin 0 → X × Answer₂ := fun i => Fin.elim0 i
      let root : S → Sum (Option Output) X := fun z =>
        replayOutcomeAction (program z.1) emptyHistory
      have hroot : Measurable root := by
        exact (hprogram 0).comp (measurable_fst.prodMk measurable_const)
      let transformedAnswer : S → Answer₂ := fun z =>
        (root z).elim (fun _ => default)
          (fun point => transform (z.1, point, (z.2 0).2))
      have htransformedAnswer : Measurable transformedAnswer := by
        exact measurable_sum_cases root hroot
          (fun _ : S × Option Output => (default : Answer₂)) measurable_const
          (fun q : S × X => transform (q.1.1, q.2, (q.1.2 0).2))
          (htransform.comp (by
            change Measurable (fun q :
                (P × (Fin (n + 1) → X × Answer₁)) × X =>
              (q.1.1, q.2, (q.1.2 0).2))
            fun_prop))
      let tailHistory : S → (Fin n → X × Answer₁) := fun z i =>
        z.2 i.succ
      have htailHistory : Measurable tailHistory := by
        rw [measurable_pi_iff]
        intro i
        change Measurable (fun z : P × (Fin (n + 1) → X × Answer₁) =>
          z.2 i.succ)
        fun_prop
      let residualFamily : P × Answer₂ →
          ExactJetProgram X Answer₂ Output := fun parameter =>
        ExactJetProgram.afterFirstAnswer (program parameter.1) parameter.2
      have hresidualFamily : IsJointlyBorelOutcome residualFamily := by
        simpa only [residualFamily] using hprogram.afterFirstAnswer default
      let residualTransform : (P × Answer₂) × (X × Answer₁) →
          Answer₂ := fun z => transform (z.1.1, z.2)
      have hresidualTransform : Measurable residualTransform :=
        htransform.comp (by fun_prop)
      have hmappedResidual : Measurable (fun z :
          (P × Answer₂) × (Fin n → X × Answer₁) =>
          replayOutcomeAction
            ((residualFamily z.1).mapAnswers (fun point answer =>
              residualTransform (z.1, point, answer))) z.2) :=
        ih hresidualFamily residualTransform hresidualTransform
      let tailOutcome : S → Sum (Option Output) X := fun z =>
        replayOutcomeAction
          ((residualFamily (z.1, transformedAnswer z)).mapAnswers
            (fun point answer => transform (z.1, point, answer))) (tailHistory z)
      have htailOutcome : Measurable tailOutcome := by
        exact hmappedResidual.comp
          ((measurable_fst.prodMk htransformedAnswer).prodMk htailHistory)
      have hcases : Measurable (fun z : S =>
          (root z).elim Sum.inl (fun _ => tailOutcome z)) := by
        exact measurable_sum_cases root hroot
          (fun q : S × Option Output => Sum.inl q.2)
          (measurable_inl.comp measurable_snd)
          (fun q : S × X => tailOutcome q.1)
          (htailOutcome.comp measurable_fst)
      convert hcases using 1
      funext z
      cases hprogramRoot : program z.1 with
      | halt result =>
          have hrootValue : root z = Sum.inl result := by
            simp [root, emptyHistory, hprogramRoot, replayOutcomeAction,
              residualAfterHistory, residualAfterAnswers]
          rw [hrootValue]
          change replayOutcomeAction
              ((program z.1).mapAnswers
                (fun point answer => transform (z.1, point, answer))) z.2 = _
          rw [hprogramRoot]
          change replayOutcomeAction (.halt result) z.2 = Sum.inl result
          simp [replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
      | query point next =>
          have hrootValue : root z = Sum.inr point := by
            simp [root, emptyHistory, hprogramRoot, replayOutcomeAction,
              residualAfterHistory, residualAfterAnswers]
          have hanswer : transformedAnswer z =
              transform (z.1, point, (z.2 0).2) := by
            simp [transformedAnswer, hrootValue]
          rw [hrootValue]
          unfold tailOutcome residualFamily
          rw [hanswer]
          change replayOutcomeAction
              ((program z.1).mapAnswers
                (fun point answer => transform (z.1, point, answer))) z.2 = _
          rw [hprogramRoot]
          change replayOutcomeAction
              (.query point (fun answer₁ =>
                (next (transform (z.1, point, answer₁))).mapAnswers
                  (fun point answer => transform (z.1, point, answer)))) z.2 =
            replayOutcomeAction
              ((next (transform (z.1, point, (z.2 0).2))).mapAnswers
                (fun point answer => transform (z.1, point, answer)))
              (tailHistory z)
          simpa only [tailHistory] using
            replayOutcomeAction_query_succ point
              (fun answer₁ =>
                (next (transform (z.1, point, answer₁))).mapAnswers
                  (fun point answer => transform (z.1, point, answer))) z.2

/-! ### Monadic sequencing -/

/-- Joint outcome measurability is preserved by a jointly measurable
continuation.  All types are kept in one universe, which is the form used by
the upper finite-dimensional programs. -/
theorem IsJointlyBorelOutcome.bind
    {X Answer A B P : Type u}
    [MeasurableSpace X] [MeasurableSpace Answer]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace P]
    [Inhabited X]
    {first : P → ExactJetProgram X Answer A}
    {next : P × A → ExactJetProgram X Answer B}
    (hfirst : IsJointlyBorelOutcome first)
    (hnext : IsJointlyBorelOutcome next) :
    IsJointlyBorelOutcome (fun parameter =>
      (first parameter).bind (fun value => next (parameter, value))) := by
  intro n
  induction n generalizing P with
  | zero =>
      let S := P × (Fin 0 → X × Answer)
      let emptyHistory : Fin 0 → X × Answer := fun i => Fin.elim0 i
      let root : S → Sum (Option A) X := fun z =>
        replayOutcomeAction (first z.1) emptyHistory
      have hroot : Measurable root := by
        simpa [S, root, emptyHistory, replayOutcomeAction,
          residualAfterHistory, residualAfterAnswers] using hfirst 0
      let successOutcome : S × A → Sum (Option B) X := fun z =>
        replayOutcomeAction (next (z.1.1, z.2)) z.1.2
      have hsuccessOutcome : Measurable successOutcome := by
        exact (hnext 0).comp (by
          change Measurable (fun z :
              (P × (Fin 0 → X × Answer)) × A =>
            ((z.1.1, z.2), z.1.2))
          fun_prop)
      let haltOutcome : S × Option A → Sum (Option B) X := fun z =>
        z.2.elim (Sum.inl none) (fun value => successOutcome (z.1, value))
      have hhaltOutcome : Measurable haltOutcome := by
        exact measurable_option_cases (fun z : S × Option A => z.2)
          measurable_snd (fun _ => Sum.inl none) measurable_const
          (fun z : (S × Option A) × A => successOutcome (z.1.1, z.2))
          (hsuccessOutcome.comp (by fun_prop))
      have hcases : Measurable (fun z : S =>
          (root z).elim (fun result => haltOutcome (z, result))
            (fun point => Sum.inr point)) := by
        exact measurable_sum_cases root hroot haltOutcome hhaltOutcome
          (fun z : S × X => Sum.inr z.2)
          (measurable_inr.comp measurable_snd)
      convert hcases using 1
      funext z
      cases hfirstRoot : first z.1 with
      | halt result =>
          cases result <;>
            simp [root, emptyHistory, haltOutcome, successOutcome,
              hfirstRoot, ExactJetProgram.bind, replayOutcomeAction,
              residualAfterHistory, residualAfterAnswers]
      | query point more =>
          simp [root, emptyHistory, hfirstRoot, ExactJetProgram.bind,
            replayOutcomeAction, residualAfterHistory, residualAfterAnswers]
  | succ n ih =>
      let S := P × (Fin (n + 1) → X × Answer)
      let emptyHistory : Fin 0 → X × Answer := fun i => Fin.elim0 i
      let root : S → Sum (Option A) X := fun z =>
        replayOutcomeAction (first z.1) emptyHistory
      have hroot : Measurable root := by
        exact (hfirst 0).comp (by
          change Measurable (fun z :
              P × (Fin (n + 1) → X × Answer) =>
            (z.1, emptyHistory))
          fun_prop)
      let successOutcome : S × A → Sum (Option B) X := fun z =>
        replayOutcomeAction (next (z.1.1, z.2)) z.1.2
      have hsuccessOutcome : Measurable successOutcome := by
        exact (hnext (n + 1)).comp (by
          change Measurable (fun z :
              (P × (Fin (n + 1) → X × Answer)) × A =>
            ((z.1.1, z.2), z.1.2))
          fun_prop)
      let haltOutcome : S × Option A → Sum (Option B) X := fun z =>
        z.2.elim (Sum.inl none) (fun value => successOutcome (z.1, value))
      have hhaltOutcome : Measurable haltOutcome := by
        exact measurable_option_cases (fun z : S × Option A => z.2)
          measurable_snd (fun _ => Sum.inl none) measurable_const
          (fun z : (S × Option A) × A => successOutcome (z.1.1, z.2))
          (hsuccessOutcome.comp (by fun_prop))
      let firstResidual : P × Answer →
          ExactJetProgram X Answer A := fun parameter =>
        ExactJetProgram.afterFirstAnswer (first parameter.1) parameter.2
      have hfirstResidual : IsJointlyBorelOutcome firstResidual := by
        simpa only [firstResidual] using hfirst.afterFirstAnswer default
      let nextResidual : (P × Answer) × A →
          ExactJetProgram X Answer B := fun parameter =>
        next (parameter.1.1, parameter.2)
      have hnextResidual : IsJointlyBorelOutcome nextResidual := by
        exact hnext.compParameter
          (fun parameter : (P × Answer) × A =>
            (parameter.1.1, parameter.2)) (by fun_prop)
      have hboundResidual : Measurable (fun z :
          (P × Answer) × (Fin n → X × Answer) =>
          replayOutcomeAction
            ((firstResidual z.1).bind (fun value =>
              nextResidual (z.1, value))) z.2) :=
        ih hfirstResidual hnextResidual
      let tailHistory : S → (Fin n → X × Answer) := fun z i =>
        z.2 i.succ
      have htailHistory : Measurable tailHistory := by
        rw [measurable_pi_iff]
        intro i
        change Measurable (fun z : P × (Fin (n + 1) → X × Answer) =>
          z.2 i.succ)
        fun_prop
      let tailOutcome : S → Sum (Option B) X := fun z =>
        replayOutcomeAction
          ((firstResidual (z.1, (z.2 0).2)).bind (fun value =>
            nextResidual ((z.1, (z.2 0).2), value))) (tailHistory z)
      have htailOutcome : Measurable tailOutcome := by
        exact hboundResidual.comp (by
          change Measurable (fun z :
              P × (Fin (n + 1) → X × Answer) =>
            ((z.1, (z.2 0).2), tailHistory z))
          fun_prop)
      have hcases : Measurable (fun z : S =>
          (root z).elim (fun result => haltOutcome (z, result))
            (fun _ => tailOutcome z)) := by
        exact measurable_sum_cases root hroot haltOutcome hhaltOutcome
          (fun z : S × X => tailOutcome z.1)
          (htailOutcome.comp measurable_fst)
      convert hcases using 1
      funext z
      cases hfirstRoot : first z.1 with
      | halt result =>
          cases result <;>
            simp [root, emptyHistory, haltOutcome, successOutcome,
              hfirstRoot, ExactJetProgram.bind, replayOutcomeAction,
              residualAfterHistory, residualAfterAnswers]
      | query point more =>
          have hrootValue : root z = Sum.inr point := by
            simp [root, emptyHistory, hfirstRoot, replayOutcomeAction,
              residualAfterHistory, residualAfterAnswers]
          rw [hrootValue]
          simp only [Sum.elim_inr]
          change replayOutcomeAction
              ((first z.1).bind (fun value => next (z.1, value))) z.2 =
            tailOutcome z
          rw [hfirstRoot]
          unfold tailOutcome firstResidual nextResidual tailHistory
          simp only [Prod.fst, Prod.snd, hfirstRoot,
            ExactJetProgram.afterFirstAnswer]
          change replayOutcomeAction
              (.query point (fun answer =>
                (more answer).bind (fun value => next (z.1, value)))) z.2 =
            replayOutcomeAction
              ((more (z.2 0).2).bind (fun value => next (z.1, value)))
              (fun i => z.2 i.succ)
          exact replayOutcomeAction_query_succ point
            (fun answer =>
              (more answer).bind (fun value => next (z.1, value))) z.2

/-- Installing a local cap commutes with compiling oracle answers. -/
theorem boost_mapAnswers_locallyCapped
    {X Answer₁ Answer₂ Output : Type*}
    (transform : X → Answer₁ → Answer₂)
    (cap : ℕ) (program : ExactJetProgram X Answer₂ Output) :
    (program.mapAnswers transform).locallyCapped cap =
      (program.locallyCapped cap).mapAnswers transform := by
  induction cap generalizing program with
  | zero => cases program <;> rfl
  | succ cap ih =>
      cases program with
      | halt result => rfl
      | query point next =>
          simp only [ExactJetProgram.mapAnswers, ExactJetProgram.locallyCapped]
          congr
          funext answer
          exact ih (next (transform point answer))

/-- Compiling answers commutes with a terminal-value map. -/
theorem boost_mapAnswers_bind_halt_some
    {X Answer₁ Answer₂ A B : Type*}
    (transform : X → Answer₁ → Answer₂)
    (program : ExactJetProgram X Answer₂ A) (finish : A → B) :
    (program.mapAnswers transform).bind
        (fun value => .halt (some (finish value))) =
      (program.bind (fun value => .halt (some (finish value)))).mapAnswers
        transform := by
  induction program with
  | halt result => cases result <;> rfl
  | query point next ih =>
      simp only [ExactJetProgram.mapAnswers, ExactJetProgram.bind]
      congr
      funext answer
      exact ih (transform point answer)

end ExactJetProgram

/-! ### Jointly measurable boost arithmetic -/

section BoostArithmetic

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every positive-order derivative of the affine regularizer is independent
of both its center and its evaluation point. -/
theorem affineRegularizer_iteratedFDeriv_joint_independent
    (eta : ℝ) (n : ℕ) (hn : 0 < n)
    (center₁ center₂ point₁ point₂ : E) :
    iteratedFDeriv ℝ n (affineRegularizer eta center₁) point₁ =
      iteratedFDeriv ℝ n (affineRegularizer eta center₂) point₂ := by
  have h₁ : ContDiffAt ℝ n (fun z : E => z - center₁) point₁ :=
    (contDiff_id.sub contDiff_const).contDiffAt.of_le le_top
  have h₂ : ContDiffAt ℝ n (fun z : E => z - center₂) point₂ :=
    (contDiff_id.sub contDiff_const).contDiffAt.of_le le_top
  change iteratedFDeriv ℝ n
      (fun z : E => (1 / eta) • (z - center₁)) point₁ =
    iteratedFDeriv ℝ n
      (fun z : E => (1 / eta) • (z - center₂)) point₂
  rw [iteratedFDeriv_const_smul_apply' h₁,
    iteratedFDeriv_const_smul_apply' h₂]
  congr 1
  rw [show (fun z : E => z - center₁) =
      (id : E → E) - fun _ => center₁ by rfl]
  rw [show (fun z : E => z - center₂) =
      (id : E → E) - fun _ => center₂ by rfl]
  rw [iteratedFDeriv_sub_apply contDiff_id.contDiffAt contDiffAt_const,
    iteratedFDeriv_sub_apply contDiff_id.contDiffAt contDiffAt_const]
  rw [iteratedFDeriv_id_independent n hn point₁ point₂]
  have hc₁ : iteratedFDeriv ℝ n (fun _ : E => center₁) = 0 :=
    iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn) center₁
  have hc₂ : iteratedFDeriv ℝ n (fun _ : E => center₂) = 0 :=
    iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn) center₂
  rw [congrFun hc₁ point₁, congrFun hc₂ point₂]
  simp

/-- The known affine jet is jointly continuous in center and query point. -/
theorem continuous_affineRegularizerJet_joint (p : ℕ) (eta : ℝ) :
    Continuous (fun z : E × E => affineRegularizerJet p eta z.1 z.2) := by
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  change Continuous (fun z : E × E =>
    iteratedFDeriv ℝ j.1 (affineRegularizer eta z.1) z.2)
  by_cases hj : j.1 = 0
  · rw [hj]
    have hregularizer : Continuous (fun z : E × E =>
        affineRegularizer eta z.1 z.2) := by
      unfold affineRegularizer
      fun_prop
    exact (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp
      hregularizer
  · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
    have heq : (fun z : E × E =>
        iteratedFDeriv ℝ j.1 (affineRegularizer eta z.1) z.2) =
        fun _ => iteratedFDeriv ℝ j.1 (affineRegularizer eta 0) 0 := by
      funext z
      exact affineRegularizer_iteratedFDeriv_joint_independent
        eta j.1 hjpos z.1 0 z.2 0
    rw [heq]
    exact continuous_const

/-- Componentwise-Borel form of the joint regularized-answer arithmetic. -/
theorem measurable_regularizedJetAnswer_withCenter
    (data : VIPublicData E) (eta : ℝ) :
    Measurable (fun z :
        data.X × (data.X × SymmetricExactJet E data.p) =>
      regularizedJetAnswer data.p eta z.1.1 z.2.1.1 z.2.2) := by
  have h := show
    @Measurable
      (data.X × (data.X × SymmetricExactJet E data.p))
      (SymmetricExactJet E data.p)
      ((upperFeasibleBorelMeasurableSpace data).prod
        ((upperFeasibleBorelMeasurableSpace data).prod
          (upperJetBorelMeasurableSpace data.p)))
      (upperJetBorelMeasurableSpace data.p)
      (fun z => regularizedJetAnswer data.p eta z.1.1 z.2.1.1 z.2.2) by
      letI : MeasurableSpace E := borel E
      letI : BorelSpace E := ⟨rfl⟩
      letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
      letI : BorelSpace data.X :=
        Subtype.borelSpace (fun x : E => x ∈ data.X)
      letI : MeasurableSpace (SymmetricExactJet E data.p) :=
        upperJetBorelMeasurableSpace data.p
      letI : BorelSpace (SymmetricExactJet E data.p) := ⟨rfl⟩
      apply Continuous.measurable
      exact (continuous_addSymmetricJet data.p).comp
        ((continuous_snd.comp continuous_snd).prodMk
          ((continuous_affineRegularizerJet_joint data.p eta).comp
            ((continuous_subtype_val.comp continuous_fst).prodMk
              (continuous_subtype_val.comp
                (continuous_fst.comp continuous_snd)))))
  rw [← upperSymmetricExactJet_measurable_eq_normBorel data.p,
    ← upperFeasible_measurable_eq_normBorel data] at h
  exact h

/-- Joint recovery before the final residual check. -/
theorem measurable_recoverBaseCertificate_joint_upper
    (data : VIPublicData E) (eta : ℝ) :
    @Measurable (E × EvaluatedNormalCertificate data)
      (EvaluatedNormalCertificate data)
      ((borel E).prod (upperEvaluatedNormalCertificateMeasurableSpace data))
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      (fun z => recoverBaseCertificate data eta z.1 z.2) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : BorelSpace data.X :=
    Subtype.borelSpace (fun x : E => x ∈ data.X)
  letI : MeasurableSpace (EvaluatedNormalCertificate data) :=
    upperEvaluatedNormalCertificateMeasurableSpace data
  have hpoint := (measurable_evaluatedNormalCertificate_point data).comp
    (measurable_snd : Measurable (Prod.snd :
      E × EvaluatedNormalCertificate data → EvaluatedNormalCertificate data))
  have hnormal := (measurable_evaluatedNormalCertificate_normal data).comp
    (measurable_snd : Measurable (Prod.snd :
      E × EvaluatedNormalCertificate data → EvaluatedNormalCertificate data))
  have hvalue := (measurable_evaluatedNormalCertificate_value data).comp
    (measurable_snd : Measurable (Prod.snd :
      E × EvaluatedNormalCertificate data → EvaluatedNormalCertificate data))
  have hpointVal : @Measurable (E × EvaluatedNormalCertificate data) E
      ((borel E).prod (upperEvaluatedNormalCertificateMeasurableSpace data))
      (borel E) (fun z => z.2.point.1) :=
    continuous_subtype_val.measurable.comp hpoint
  have hregularizer : @Measurable
      (E × EvaluatedNormalCertificate data) E
      ((borel E).prod (upperEvaluatedNormalCertificateMeasurableSpace data))
      (borel E) (fun z => affineRegularizer eta z.1 z.2.point.1) := by
    unfold affineRegularizer
    exact (hpointVal.sub measurable_fst).const_smul (1 / eta)
  exact @measurable_evaluatedNormalCertificate_mk E _ _ _
    (E × EvaluatedNormalCertificate data)
    ((borel E).prod (upperEvaluatedNormalCertificateMeasurableSpace data))
    data (fun z => z.2.point) (fun z => z.2.normal)
    (fun z => z.2.value - affineRegularizer eta z.1 z.2.point.1)
    hpoint hnormal (hvalue.sub hregularizer)

/-- The final check is jointly measurable in its regularization center and
the returned certificate. -/
theorem measurable_checkedRecoveredCertificate_joint_upper
    (data : VIPublicData E) (eta epsilon : ℝ) :
    @Measurable (E × EvaluatedNormalCertificate data)
      (Option (EvaluatedNormalCertificate data))
      ((borel E).prod (upperEvaluatedNormalCertificateMeasurableSpace data))
      (upperOptionalEvaluatedNormalCertificateMeasurableSpace data)
      (fun z => checkedRecoveredCertificate data eta epsilon z.1 z.2) := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (EvaluatedNormalCertificate data) :=
    upperEvaluatedNormalCertificateMeasurableSpace data
  rw [measurable_comap_iff]
  unfold checkedRecoveredCertificate
  change Measurable (fun z : E × EvaluatedNormalCertificate data =>
    (Equiv.optionEquivSumPUnit (EvaluatedNormalCertificate data))
      (if ‖(recoverBaseCertificate data eta z.1 z.2).value +
          (recoverBaseCertificate data eta z.1 z.2).normal‖ ≤ epsilon then
        some (recoverBaseCertificate data eta z.1 z.2)
      else none))
  simp only [apply_ite, Equiv.optionEquivSumPUnit_some,
    Equiv.optionEquivSumPUnit_none]
  have hrecover := measurable_recoverBaseCertificate_joint_upper data eta
  have hresidual := (measurable_certificate_residual data).comp hrecover
  apply Measurable.ite (measurableSet_le hresidual measurable_const)
  · exact measurable_inl.comp hrecover
  · exact measurable_inr.comp (measurable_const : Measurable
      (fun _ : E × EvaluatedNormalCertificate data => PUnit.unit))

/-! ### Concrete capped boost programs -/

local instance upperCertificateMeasurableSpace_boost
    (data : VIPublicData E) :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  upperEvaluatedNormalCertificateMeasurableSpace data

local instance feasibleInhabited_boost (data : VIPublicData E) :
    Inhabited data.X :=
  ⟨⟨data.x0, data.x0_mem⟩⟩

local instance jetInhabited_boost (data : VIPublicData E) :
    Inhabited (SymmetricExactJet E data.p) :=
  ⟨fun _ => ⟨0, by intro σ; rfl⟩⟩

theorem ExactJetProgram.boost_bind_assoc
    {X Answer A B C : Type*}
    (program : ExactJetProgram X Answer A)
    (next : A → ExactJetProgram X Answer B)
    (last : B → ExactJetProgram X Answer C) :
    (program.bind next).bind last =
      program.bind (fun value => (next value).bind last) := by
  induction program with
  | halt result => cases result <;> rfl
  | query point more ih =>
      simp only [ExactJetProgram.bind]
      congr
      funext answer
      exact ih answer

def boostWithStartPoint (data : VIPublicData E) (anchor x : data.X) :
    (data.withStart anchor).X :=
  ⟨x.1, x.2⟩

@[simp] theorem boostWithStartPoint_val (data : VIPublicData E)
    (anchor x : data.X) :
    (boostWithStartPoint data anchor x).1 = x.1 := rfl

@[simp] theorem boostWithStartPoint_fromCertificate
    (data : VIPublicData E) (anchor : data.X)
    (cert : EvaluatedNormalCertificate (data.withStart anchor)) :
    boostWithStartPoint data anchor (cert.fromWithStart data anchor).point =
      cert.point := by
  apply Subtype.ext
  rfl

theorem boostWithStartPoint_compactProjection (data : VIPublicData E)
    (anchor : data.X) (z : E) :
    boostWithStartPoint data anchor (compactProjection data z) =
      compactProjection (data.withStart anchor) z := by
  apply Subtype.ext
  rfl

/-- A compiled strong subcall with its shifted certificate transported back
to one fixed public datum. -/
def transportedCompiledStrongProgram {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (eta delta : ℝ)
    (state : data.X × (data.X × data.X)) :
    ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) :=
  (compiledStrongProgram (data.withStart state.1)
      (boostedStrongAt family data hp state.1) eta delta
      state.2.1 state.2.2).bind
    (fun cert => .halt (some (cert.fromWithStart data state.1)))

theorem transportedCompiledStrongProgram_isJointlyBorelOutcome {p : ℕ}
    (family : StrongSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p) (eta delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (transportedCompiledStrongProgram family data hp eta delta) := by
  let baseProgram : data.X × data.X →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data) := fun state =>
    let shifted := data.withStart state.1
    let call := (family.atData shifted hp).solve state.2 (1 / eta) delta
    call.anchoredInstalledProgram data state.1
  have hbase : ExactJetProgram.IsJointlyBorelOutcome baseProgram := by
    simpa only [baseProgram] using hfamily.2 E data hp (1 / eta) delta
  let selectedBase : data.X × (data.X × data.X) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data) := fun state =>
    baseProgram (state.1, state.2.2)
  have hselected : ExactJetProgram.IsJointlyBorelOutcome selectedBase :=
    hbase.compParameter (fun state : data.X × (data.X × data.X) =>
      (state.1, state.2.2)) (by fun_prop)
  let transform :
      (data.X × (data.X × data.X)) ×
        (data.X × SymmetricExactJet E data.p) →
          SymmetricExactJet E data.p := fun z =>
    regularizedJetAnswer data.p eta z.1.2.1.1 z.2.1.1 z.2.2
  have htransform : Measurable transform :=
    (measurable_regularizedJetAnswer_withCenter data eta).comp (by
      change Measurable (fun z :
          (data.X × (data.X × data.X)) ×
            (data.X × SymmetricExactJet E data.p) =>
        (z.1.2.1, z.2))
      fun_prop)
  have hmapped := hselected.mapAnswersWithParameter transform htransform
  convert hmapped using 1
  funext state
  unfold transportedCompiledStrongProgram selectedBase baseProgram
  simp only [boostedStrongAt, compiledStrongProgram, compileRegularizedCall,
    CappedExactJetCall.anchoredInstalledProgram,
    CappedExactJetCall.installedProgram, CappedExactJetCall.fromWithStart,
    VIPublicData.withStart]
  rw [ExactJetProgram.locallyCapped_mapAnswers_bind_halt_some]

theorem transportedCompiledStrongProgram_eq {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (eta delta : ℝ)
    (anchor center warm : data.X) :
    transportedCompiledStrongProgram family data hp eta delta
        (anchor, center, warm) =
      (by
        simpa only [VIPublicData.withStart] using
          (compiledStrongProgram (data.withStart anchor)
            (boostedStrongAt family data hp anchor) eta delta
            (boostWithStartPoint data anchor center)
            (boostWithStartPoint data anchor warm)).bind
              (fun cert => .halt
                (some (cert.fromWithStart data anchor)))) := by
  unfold transportedCompiledStrongProgram
  rfl

theorem measurable_boostWarmPoint (data : VIPublicData E) :
    Measurable (fun z : data.X × data.X =>
      compactProjection data ((2 : ℝ) • z.1.1 - z.2.1)) := by
  have h : @Measurable (data.X × data.X) data.X
      ((upperFeasibleBorelMeasurableSpace data).prod
        (upperFeasibleBorelMeasurableSpace data))
      (upperFeasibleBorelMeasurableSpace data)
      (fun z => compactProjection data ((2 : ℝ) • z.1.1 - z.2.1)) := by
    letI : MeasurableSpace E := borel E
    letI : BorelSpace E := ⟨rfl⟩
    letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
    letI : BorelSpace data.X :=
      Subtype.borelSpace (fun x : E => x ∈ data.X)
    exact (continuous_compactProjection data).measurable.comp (by fun_prop)
  rw [← upperFeasible_measurable_eq_normBorel data] at h
  exact h

def anchoredFeasibleHalpernUpdate (data : VIPublicData E) (t : ℕ)
    (z : data.X × data.X) : data.X :=
  ⟨(1 / (t + 2 : ℝ)) • z.1.1 +
      ((t + 1 : ℝ) / (t + 2 : ℝ)) • z.2.1, by
    apply data.X_convex z.1.2 z.2.2 <;> try positivity
    field_simp
    ring⟩

theorem boostWithStartPoint_anchoredFeasibleHalpernUpdate
    (data : VIPublicData E) (anchor y : data.X) (t : ℕ) :
    boostWithStartPoint data anchor
        (anchoredFeasibleHalpernUpdate data t (anchor, y)) =
      feasibleHalpernUpdate (data.withStart anchor) t
        (boostWithStartPoint data anchor y) := by
  apply Subtype.ext
  rfl

theorem measurable_anchoredFeasibleHalpernUpdate
    (data : VIPublicData E) (t : ℕ) :
    Measurable (anchoredFeasibleHalpernUpdate data t) := by
  have h : @Measurable (data.X × data.X) data.X
      ((upperFeasibleBorelMeasurableSpace data).prod
        (upperFeasibleBorelMeasurableSpace data))
      (upperFeasibleBorelMeasurableSpace data)
      (anchoredFeasibleHalpernUpdate data t) := by
    letI : MeasurableSpace E := borel E
    letI : BorelSpace E := ⟨rfl⟩
    letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
    letI : BorelSpace data.X :=
      Subtype.borelSpace (fun x : E => x ∈ data.X)
    apply Continuous.measurable
    unfold anchoredFeasibleHalpernUpdate
    fun_prop
  rw [← upperFeasible_measurable_eq_normBorel data] at h
  exact h

def transportedExtrapolatedHalpernTail {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (eta delta epsilon : ℝ) :
    (remaining t : ℕ) →
      data.X × (data.X × (data.X × data.X)) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data)
  | 0, _, state =>
      let anchor := state.1
      let center := state.2.1
      let previous := state.2.2.1
      let before := state.2.2.2
      let warm := compactProjection data ((2 : ℝ) • previous.1 - before.1)
      (transportedCompiledStrongProgram family data hp eta delta
        (anchor, center, warm)).bind (fun cert =>
          .halt (checkedRecoveredCertificate data eta epsilon center.1 cert))
  | remaining + 1, t, state =>
      let anchor := state.1
      let center := state.2.1
      let previous := state.2.2.1
      let before := state.2.2.2
      let warm := compactProjection data ((2 : ℝ) • previous.1 - before.1)
      (transportedCompiledStrongProgram family data hp eta delta
        (anchor, center, warm)).bind (fun cert =>
          transportedExtrapolatedHalpernTail family data hp eta delta epsilon
            remaining (t + 1)
            (anchor,
              anchoredFeasibleHalpernUpdate data t (anchor, cert.point),
              cert.point, previous))

theorem transportedExtrapolatedHalpernTail_isJointlyBorelOutcome {p : ℕ}
    (family : StrongSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p)
    (eta delta epsilon : ℝ) (remaining t : ℕ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (transportedExtrapolatedHalpernTail family data hp eta delta epsilon
        remaining t) := by
  induction remaining generalizing t with
  | zero =>
      let State := data.X × (data.X × (data.X × data.X))
      let first : State → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) :=
        fun state => transportedCompiledStrongProgram family data hp eta delta
          (state.1, state.2.1,
            compactProjection data
              ((2 : ℝ) • state.2.2.1.1 - state.2.2.2.1))
      have hfirst : ExactJetProgram.IsJointlyBorelOutcome first :=
        (transportedCompiledStrongProgram_isJointlyBorelOutcome
          family hfamily data hp eta delta).compParameter
          (fun state : State =>
            (state.1, state.2.1,
              compactProjection data
                ((2 : ℝ) • state.2.2.1.1 - state.2.2.2.1))) (by
            exact measurable_fst.prodMk
              ((measurable_fst.comp measurable_snd).prodMk
                ((measurable_boostWarmPoint data).comp (by fun_prop))))
      let next : State × EvaluatedNormalCertificate data →
          ExactJetProgram data.X (SymmetricExactJet E data.p)
            (EvaluatedNormalCertificate data) := fun z =>
        .halt (checkedRecoveredCertificate data eta epsilon z.1.2.1.1 z.2)
      have hnext : ExactJetProgram.IsJointlyBorelOutcome next := by
        apply ExactJetProgram.isJointlyBorelOutcome_halt
        have hcenter : @Measurable
            (State × EvaluatedNormalCertificate data) E inferInstance (borel E)
            (fun z => z.1.2.1.1) := by
          rw [← (BorelSpace.measurable_eq :
            (‹MeasurableSpace E›) = borel E)]
          change Measurable (fun z :
            (data.X × (data.X × (data.X × data.X))) ×
              EvaluatedNormalCertificate data => z.1.2.1.1)
          fun_prop
        exact (measurable_checkedRecoveredCertificate_joint_upper
          data eta epsilon).comp (hcenter.prodMk measurable_snd)
      have hbound := hfirst.bind hnext
      simpa only [transportedExtrapolatedHalpernTail, State, first, next]
        using hbound
  | succ remaining ih =>
      let State := data.X × (data.X × (data.X × data.X))
      let first : State → ExactJetProgram data.X
          (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) :=
        fun state => transportedCompiledStrongProgram family data hp eta delta
          (state.1, state.2.1,
            compactProjection data
              ((2 : ℝ) • state.2.2.1.1 - state.2.2.2.1))
      have hfirst : ExactJetProgram.IsJointlyBorelOutcome first :=
        (transportedCompiledStrongProgram_isJointlyBorelOutcome
          family hfamily data hp eta delta).compParameter
          (fun state : State =>
            (state.1, state.2.1,
              compactProjection data
                ((2 : ℝ) • state.2.2.1.1 - state.2.2.2.1))) (by
            exact measurable_fst.prodMk
              ((measurable_fst.comp measurable_snd).prodMk
                ((measurable_boostWarmPoint data).comp (by fun_prop))))
      let next : State × EvaluatedNormalCertificate data →
          ExactJetProgram data.X (SymmetricExactJet E data.p)
            (EvaluatedNormalCertificate data) := fun z =>
        transportedExtrapolatedHalpernTail family data hp eta delta epsilon
          remaining (t + 1)
          (z.1.1,
            anchoredFeasibleHalpernUpdate data t (z.1.1, z.2.point),
            z.2.point, z.1.2.2.1)
      have hpoint : Measurable
          (EvaluatedNormalCertificate.point :
            EvaluatedNormalCertificate data → data.X) := by
        have h := measurable_evaluatedNormalCertificate_point data
        rw [← upperFeasible_measurable_eq_normBorel data] at h
        exact h
      have hnext : ExactJetProgram.IsJointlyBorelOutcome next :=
        ih (t + 1) |>.compParameter
          (fun z : State × EvaluatedNormalCertificate data =>
            (z.1.1,
              anchoredFeasibleHalpernUpdate data t (z.1.1, z.2.point),
              z.2.point, z.1.2.2.1)) (by
            exact (measurable_fst.comp measurable_fst).prodMk
              (((measurable_anchoredFeasibleHalpernUpdate data t).comp
                ((measurable_fst.comp measurable_fst).prodMk
                  (hpoint.comp measurable_snd))).prodMk
                ((hpoint.comp measurable_snd).prodMk
                  (measurable_fst.comp
                    (measurable_snd.comp (measurable_snd.comp measurable_fst))))))
      have hbound := hfirst.bind hnext
      simpa only [transportedExtrapolatedHalpernTail, State, first, next]
        using hbound

def transportedExtrapolatedHalpernProgram {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (K : ℕ) (eta delta epsilon : ℝ)
    (anchor : data.X) :
    ExactJetProgram data.X (SymmetricExactJet E data.p)
      (EvaluatedNormalCertificate data) :=
  (transportedCompiledStrongProgram family data hp eta delta
      (anchor, anchor, anchor)).bind (fun cert₀ =>
    (transportedCompiledStrongProgram family data hp eta delta
      (anchor, anchoredFeasibleHalpernUpdate data 0 (anchor, cert₀.point),
        cert₀.point)).bind (fun cert₁ =>
      transportedExtrapolatedHalpernTail family data hp eta delta epsilon
        (K - 2) 2
        (anchor, anchoredFeasibleHalpernUpdate data 1 (anchor, cert₁.point),
          cert₁.point, cert₀.point)))

theorem transportedExtrapolatedHalpernProgram_isJointlyBorelOutcome {p : ℕ}
    (family : StrongSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p)
    (K : ℕ) (eta delta epsilon : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (transportedExtrapolatedHalpernProgram family data hp K eta delta epsilon) := by
  have hpoint : Measurable
      (EvaluatedNormalCertificate.point :
        EvaluatedNormalCertificate data → data.X) := by
    have h := measurable_evaluatedNormalCertificate_point data
    rw [← upperFeasible_measurable_eq_normBorel data] at h
    exact h
  let first : data.X → ExactJetProgram data.X
      (SymmetricExactJet E data.p) (EvaluatedNormalCertificate data) :=
    fun anchor => transportedCompiledStrongProgram family data hp eta delta
      (anchor, anchor, anchor)
  have hfirst : ExactJetProgram.IsJointlyBorelOutcome first :=
    (transportedCompiledStrongProgram_isJointlyBorelOutcome
      family hfamily data hp eta delta).compParameter
      (fun anchor : data.X => (anchor, anchor, anchor)) (by fun_prop)
  let second : (data.X × EvaluatedNormalCertificate data) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data) := fun z =>
    transportedCompiledStrongProgram family data hp eta delta
      (z.1, anchoredFeasibleHalpernUpdate data 0 (z.1, z.2.point), z.2.point)
  have hsecond : ExactJetProgram.IsJointlyBorelOutcome second :=
    (transportedCompiledStrongProgram_isJointlyBorelOutcome
      family hfamily data hp eta delta).compParameter
      (fun z : data.X × EvaluatedNormalCertificate data =>
        (z.1, anchoredFeasibleHalpernUpdate data 0 (z.1, z.2.point),
          z.2.point)) (by
        exact measurable_fst.prodMk
          (((measurable_anchoredFeasibleHalpernUpdate data 0).comp
            (measurable_fst.prodMk (hpoint.comp measurable_snd))).prodMk
              (hpoint.comp measurable_snd)))
  let tail : ((data.X × EvaluatedNormalCertificate data) ×
      EvaluatedNormalCertificate data) →
      ExactJetProgram data.X (SymmetricExactJet E data.p)
        (EvaluatedNormalCertificate data) := fun z =>
    transportedExtrapolatedHalpernTail family data hp eta delta epsilon
      (K - 2) 2
      (z.1.1, anchoredFeasibleHalpernUpdate data 1 (z.1.1, z.2.point),
        z.2.point, z.1.2.point)
  have htail : ExactJetProgram.IsJointlyBorelOutcome tail :=
    (transportedExtrapolatedHalpernTail_isJointlyBorelOutcome
      family hfamily data hp eta delta epsilon (K - 2) 2).compParameter
      (fun z : (data.X × EvaluatedNormalCertificate data) ×
          EvaluatedNormalCertificate data =>
        (z.1.1, anchoredFeasibleHalpernUpdate data 1 (z.1.1, z.2.point),
          z.2.point, z.1.2.point)) (by
        exact (measurable_fst.comp measurable_fst).prodMk
          (((measurable_anchoredFeasibleHalpernUpdate data 1).comp
            ((measurable_fst.comp measurable_fst).prodMk
              (hpoint.comp measurable_snd))).prodMk
            ((hpoint.comp measurable_snd).prodMk
              (hpoint.comp (measurable_snd.comp measurable_fst)))))
  have hrest := hsecond.bind htail
  have hall := hfirst.bind hrest
  convert hall using 1
  funext anchor
  rfl

theorem checkedRecoveredCertificate_fromWithStart
    (data : VIPublicData E) (anchor : data.X)
    (eta epsilon : ℝ) (center : E)
    (cert : EvaluatedNormalCertificate (data.withStart anchor)) :
    Option.map (fun output => output.fromWithStart data anchor)
        (checkedRecoveredCertificate (data.withStart anchor)
          eta epsilon center cert) =
      checkedRecoveredCertificate data eta epsilon center
        (cert.fromWithStart data anchor) := by
  let shiftedRecovered := recoverBaseCertificate (data.withStart anchor)
    eta center cert
  let baseRecovered := recoverBaseCertificate data eta center
    (cert.fromWithStart data anchor)
  have hrecovered : shiftedRecovered.fromWithStart data anchor =
      baseRecovered := by
    cases cert
    rfl
  have hnorm : ‖shiftedRecovered.value + shiftedRecovered.normal‖ =
      ‖baseRecovered.value + baseRecovered.normal‖ := by
    rw [← hrecovered]
    rfl
  unfold checkedRecoveredCertificate
  change Option.map (fun output => output.fromWithStart data anchor)
      (if ‖shiftedRecovered.value + shiftedRecovered.normal‖ ≤ epsilon then
        some shiftedRecovered else none) =
    (if ‖baseRecovered.value + baseRecovered.normal‖ ≤ epsilon then
      some baseRecovered else none)
  rw [hnorm]
  split <;> simp_all

theorem transportedExtrapolatedHalpernTail_eq {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (eta delta epsilon : ℝ)
    (remaining t : ℕ) (anchor center previous before : data.X) :
    transportedExtrapolatedHalpernTail family data hp eta delta epsilon
        remaining t (anchor, center, previous, before) =
      (extrapolatedHalpernTail (data.withStart anchor)
        (boostedStrongAt family data hp anchor) eta delta epsilon remaining t
        (boostWithStartPoint data anchor center)
        (boostWithStartPoint data anchor previous)
        (boostWithStartPoint data anchor before)).bind
          (fun cert => .halt (some (cert.fromWithStart data anchor))) := by
  induction remaining generalizing t center previous before with
  | zero =>
      simp only [transportedExtrapolatedHalpernTail,
        extrapolatedHalpernTail]
      rw [transportedCompiledStrongProgram_eq]
      simp only [VIPublicData.withStart, boostWithStartPoint] at *
      rw [ExactJetProgram.boost_bind_assoc,
        ExactJetProgram.boost_bind_assoc]
      congr 1
      funext cert
      simp only [ExactJetProgram.bind]
      have hcommute := checkedRecoveredCertificate_fromWithStart
        data anchor eta epsilon (boostWithStartPoint data anchor center).1 cert
      simp only [VIPublicData.withStart, boostWithStartPoint_val] at hcommute
      cases hresult : checkedRecoveredCertificate (data.withStart anchor)
          eta epsilon (boostWithStartPoint data anchor center).1 cert with
      | none =>
          simp only [VIPublicData.withStart, boostWithStartPoint_val] at hresult
          rw [hresult] at hcommute ⊢
          simp only [Option.map_none] at hcommute
          rw [← hcommute]
          rfl
      | some result =>
          simp only [VIPublicData.withStart, boostWithStartPoint_val] at hresult
          rw [hresult] at hcommute ⊢
          simp only [Option.map_some] at hcommute
          rw [← hcommute]
          rfl
  | succ remaining ih =>
      simp only [transportedExtrapolatedHalpernTail,
        extrapolatedHalpernTail]
      rw [transportedCompiledStrongProgram_eq]
      simp only [VIPublicData.withStart, boostWithStartPoint] at *
      rw [ExactJetProgram.boost_bind_assoc,
        ExactJetProgram.boost_bind_assoc]
      congr 1
      funext cert
      simp only [ExactJetProgram.bind]
      have hcenter : boostWithStartPoint data anchor
          (anchoredFeasibleHalpernUpdate data t
            (anchor, (cert.fromWithStart data anchor).point)) =
          feasibleHalpernUpdate (data.withStart anchor) t cert.point := by
        rw [boostWithStartPoint_anchoredFeasibleHalpernUpdate,
          boostWithStartPoint_fromCertificate]
      have hprevious : boostWithStartPoint data anchor
          (cert.fromWithStart data anchor).point = cert.point :=
        boostWithStartPoint_fromCertificate data anchor cert
      simp only [VIPublicData.withStart, boostWithStartPoint] at hcenter hprevious
      have htail := ih (t + 1)
        (anchoredFeasibleHalpernUpdate data t
          (anchor, (cert.fromWithStart data anchor).point))
        (cert.fromWithStart data anchor).point previous
      rw [hcenter, hprevious] at htail
      exact htail

theorem transportedExtrapolatedHalpernProgram_eq {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (K : ℕ) (eta delta epsilon : ℝ)
    (anchor : data.X) :
    transportedExtrapolatedHalpernProgram family data hp K eta delta epsilon
        anchor =
      (extrapolatedHalpernProgram (data.withStart anchor)
        (boostedStrongAt family data hp anchor) K eta delta epsilon).bind
          (fun cert => .halt (some (cert.fromWithStart data anchor))) := by
  unfold transportedExtrapolatedHalpernProgram extrapolatedHalpernProgram
  rw [transportedCompiledStrongProgram_eq]
  simp only [VIPublicData.withStart, boostWithStartPoint] at *
  rw [ExactJetProgram.boost_bind_assoc,
    ExactJetProgram.boost_bind_assoc]
  congr 1
  funext cert₀
  simp only [ExactJetProgram.bind]
  rw [transportedCompiledStrongProgram_eq]
  simp only [VIPublicData.withStart, boostWithStartPoint] at *
  rw [ExactJetProgram.boost_bind_assoc,
    ExactJetProgram.boost_bind_assoc]
  congr 1
  funext cert₁
  simp only [ExactJetProgram.bind]
  have hcenter₁ : boostWithStartPoint data anchor
      (anchoredFeasibleHalpernUpdate data 1
        (anchor, (cert₁.fromWithStart data anchor).point)) =
      feasibleHalpernUpdate (data.withStart anchor) 1 cert₁.point := by
    rw [boostWithStartPoint_anchoredFeasibleHalpernUpdate,
      boostWithStartPoint_fromCertificate]
  have hprevious₁ : boostWithStartPoint data anchor
      (cert₁.fromWithStart data anchor).point = cert₁.point :=
    boostWithStartPoint_fromCertificate data anchor cert₁
  have hbefore₀ : boostWithStartPoint data anchor
      (cert₀.fromWithStart data anchor).point = cert₀.point :=
    boostWithStartPoint_fromCertificate data anchor cert₀
  simp only [VIPublicData.withStart, boostWithStartPoint] at hcenter₁ hprevious₁ hbefore₀
  have htail := transportedExtrapolatedHalpernTail_eq family data hp
    eta delta epsilon (K - 2) 2 anchor
    (anchoredFeasibleHalpernUpdate data 1
      (anchor, (cert₁.fromWithStart data anchor).point))
    (cert₁.fromWithStart data anchor).point
    (cert₀.fromWithStart data anchor).point
  simp only [VIPublicData.withStart, boostWithStartPoint] at htail
  rw [hcenter₁, hprevious₁, hbefore₀] at htail
  exact htail

def boostedResidualInstalledCap {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (gamma : ℝ) (b : ℕ) (R epsilon : ℝ) : ℕ :=
  let K := boostHorizon data gamma R epsilon
  let eta := boostStepsize R epsilon K
  let e := boostOuterError R K
  boostSharedCap data (family.atData data hp) gamma b K R eta e

theorem boostedResidualSolve_installedProgram_eq {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (gamma : ℝ) (b : ℕ) (R epsilon : ℝ)
    (center : data.X) :
    (boostedResidualSolve family gamma b data hp center R epsilon).installedProgram
        data =
      (transportedExtrapolatedHalpernProgram family data hp
        (boostHorizon data gamma R epsilon)
        (boostStepsize R epsilon (boostHorizon data gamma R epsilon))
        (boostOuterError R (boostHorizon data gamma R epsilon) /
          boostStepsize R epsilon (boostHorizon data gamma R epsilon))
        epsilon center).locallyCapped
          (boostedResidualInstalledCap family data hp gamma b R epsilon) := by
  rw [transportedExtrapolatedHalpernProgram_eq]
  unfold boostedResidualSolve boostedResidualCall extrapolatedHalpernCall
    CappedExactJetCall.installedProgram CappedExactJetCall.fromWithStart
    boostedResidualInstalledCap
  rfl

theorem boostedResidualSolve_anchoredInstalledProgram_eq {p : ℕ}
    (family : StrongSolverFamily.{u} p) (data : VIPublicData E)
    (hp : data.p = p) (gamma : ℝ) (b : ℕ) (R epsilon : ℝ)
    (anchor center : data.X) :
    (boostedResidualSolve family gamma b (data.withStart anchor) hp
        center R epsilon).anchoredInstalledProgram data anchor =
      (boostedResidualSolve family gamma b data hp center R epsilon).installedProgram
        data := by
  unfold CappedExactJetCall.anchoredInstalledProgram boostedResidualSolve
  rw [CappedExactJetCall.fromWithStart_fromWithStart]
  rfl

theorem boostedResidualFamily_hasJointBorelCappedOutcome
    (p : ℕ) (family : StrongSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (gamma : ℝ) (b : ℕ) :
    (boostedResidualFamily p family gamma b).HasJointBorelCappedOutcome := by
  have hordinary : ∀ (E : Type u) [NormedAddCommGroup E]
      [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome
        (fun center : data.X =>
          let call := ((boostedResidualFamily p family gamma b).atData data hp).solve
            center R epsilon
          call.installedProgram data) := by
    intro E _ _ _ _ _ data hp R epsilon
    let K := boostHorizon data gamma R epsilon
    let eta := boostStepsize R epsilon K
    let e := boostOuterError R K
    have hprogram :=
      transportedExtrapolatedHalpernProgram_isJointlyBorelOutcome
        family hfamily data hp K eta (e / eta) epsilon
    have hcapped :=
      ExactJetProgram.IsJointlyBorelOutcome.locallyCappedOutcome hprogram
        (boostedResidualInstalledCap family data hp gamma b R epsilon)
    convert hcapped using 1
    funext center
    rw [boostedResidualFamily_atData_solve,
      boostedResidualSolve_installedProgram_eq]
  refine ⟨hordinary, ?_⟩
  intro E _ _ _ _ _ data hp R epsilon
  have hselected := (hordinary E data hp R epsilon).compParameter
    (fun state : data.X × data.X => state.2) measurable_snd
  convert hselected using 1
  · rfl
  · funext state
    simp only [boostedResidualFamily_atData_solve]
    exact boostedResidualSolve_anchoredInstalledProgram_eq family data hp
      gamma b R epsilon state.1 state.2

theorem boostedResidualFamily_isBorel
    (p : ℕ) (family : StrongSolverFamily.{u} p)
    (hfamily : family.HasJointBorelCappedOutcome)
    (gamma : ℝ) (b : ℕ) :
    (boostedResidualFamily p family gamma b).IsBorel :=
  (boostedResidualFamily_hasJointBorelCappedOutcome
    p family hfamily gamma b).isBorel

end BoostArithmetic

end

end LeanArticleAudit.Pilot
