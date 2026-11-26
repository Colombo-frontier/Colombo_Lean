import GradientHessian.ControllerMeasurableExecution
import GradientHessian.ComparisonControllerReplay

/-! Measurable internal phases, finite tick iteration and entry/exit
freezing. The pending point stays in its original measurable point space. -/

noncomputable section
namespace GradientHessian.ControllerMeasurable
open Classical TaskState ComparisonController ComparisonControllerPhases ComparisonControllerReplay

variable {Ω X A : Type*} {L M ell : ℕ}
variable [MeasurableSpace Ω] [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem measurable_phase_decode {T : Type*} [MeasurableSpace T]
    {p : T → Pending X} {s : T → PhaseData L M ell} (hp : Measurable p) (hs : Measurable s) :
    Measurable (fun q => (phaseEquiv L M ell X A).symm (p q,s q)) :=
  (phaseMeasurableEquiv L M ell X A).symm.measurable.comp (hp.prodMk hs)

variable (priority : List A) (target : A → FrontierState.Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a, Measurable (fun p : Ω × X => trigger p.1 s p.2 a))
  (hhit : ∀ s, Measurable (fun p : Ω × X => hit p.1 s p.2))

include htrigger hhit in
theorem tick_joint_measurable :
    Measurable (fun q : Ω × Phase L M ell X A => tick (parameterRules priority target trigger hit q.1) q.2) := by
  let step : (Ω × Pending X) × PhaseData L M ell → Phase L M ell X A := fun q =>
    tick (parameterRules priority target trigger hit q.1.1) ((phaseEquiv L M ell X A).symm (q.1.2,q.2))
  have hstep : Measurable step := by
    apply measurable_from_prod_countable
    intro s
    rcases s with s | s | ⟨before,after⟩ | s
    · let update : Option A → PhaseData L M ell := fun a => match a with
        | none => .inr (.inl s)
        | some a => .inl (retireNode s (target a))
      have hu := (measurable_of_countable update).comp
        (choose_fixed_measurable priority target trigger hit htrigger s)
      have h := measurable_phase_decode (A := A) measurable_snd hu
      convert h using 1
      funext q
      cases hc : choose (parameterRules priority target trigger hit q.1) q.2 s <;>
        simp [step,tick,phaseEquiv,update,hc] <;> rfl
    · have hn := normal_fixed_measurable priority target trigger hit hhit s
      exact measurable_phase_decode (A := A) measurable_snd
        ((measurable_of_countable (fun next : State L M ell =>
          (.inr (.inr (.inl (s,next))) : PhaseData L M ell))).comp hn)
    · exact measurable_phase_decode (A := A) measurable_snd
        (measurable_const (a := (.inr (.inr (.inl (before,after))) : PhaseData L M ell)))
    · exact measurable_phase_decode (A := A) measurable_snd
        (measurable_const (a := (.inr (.inr (.inr s)) : PhaseData L M ell)))
  have hc := (phaseMeasurableEquiv L M ell X A).measurable.comp
    (measurable_snd : Measurable (Prod.snd : Ω × Phase L M ell X A → Phase L M ell X A))
  have hp := measurable_fst.comp hc
  have hs := measurable_snd.comp hc
  have h := hstep.comp ((measurable_fst.prodMk hp).prodMk hs)
  convert h using 1
  funext q
  exact congrArg (tick (parameterRules priority target trigger hit q.1))
    ((phaseEquiv L M ell X A).symm_apply_apply q.2).symm

include htrigger hhit in
theorem ticks_joint_measurable (n : ℕ) :
    Measurable (fun q : Ω × Phase L M ell X A => ticks (parameterRules priority target trigger hit q.1) n q.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih => exact ih.comp (measurable_fst.prodMk
      (tick_joint_measurable priority target trigger hit htrigger hhit))

omit priority target trigger hit htrigger hhit in
theorem freeze_measurable (stop : State L M ell → Bool) :
    Measurable (freeze stop : Phase L M ell X A → Phase L M ell X A) := by
  let step : Pending X × PhaseData L M ell → Phase L M ell X A := fun q =>
    freeze stop ((phaseEquiv L M ell X A).symm q)
  have hstep : Measurable step := by
    apply measurable_from_prod_countable
    intro s
    rcases s with s | s | ⟨before,after⟩ | s
    · by_cases h : stop s=true
      · simpa [step,phaseEquiv,freeze,h] using
          measurable_phase_decode (A := A) measurable_id
            (measurable_const (a := (.inr (.inr (.inr s)) : PhaseData L M ell)))
      · simpa [step,phaseEquiv,freeze,h] using
          measurable_phase_decode (A := A) measurable_id (measurable_const (a := (.inl s : PhaseData L M ell)))
    · by_cases h : stop s=true
      · simpa [step,phaseEquiv,freeze,h] using
          measurable_phase_decode (A := A) measurable_id
            (measurable_const (a := (.inr (.inr (.inr s)) : PhaseData L M ell)))
      · simpa [step,phaseEquiv,freeze,h] using
          measurable_phase_decode (A := A) measurable_id
            (measurable_const (a := (.inr (.inl s) : PhaseData L M ell)))
    · by_cases h : stop after=true
      · simpa [step,phaseEquiv,freeze,h] using
          measurable_phase_decode (A := A) measurable_id
            (measurable_const (a := (.inr (.inr (.inr after)) : PhaseData L M ell)))
      · simpa [step,phaseEquiv,freeze,h] using
          measurable_phase_decode (A := A) measurable_id
            (measurable_const (a := (.inr (.inr (.inl (before,after))) : PhaseData L M ell)))
    · exact measurable_phase_decode (A := A) (measurable_id (α := Pending X))
        (measurable_const (a := (.inr (.inr (.inr s)) : PhaseData L M ell)))
  have h := hstep.comp (phaseMeasurableEquiv L M ell X A).measurable
  convert h using 1
  funext q
  exact congrArg (freeze stop) ((phaseEquiv L M ell X A).symm_apply_apply q).symm

include htrigger hhit in
theorem guardedTick_joint_measurable (stop : State L M ell → Bool) :
    Measurable (fun q : Ω × Phase L M ell X A =>
      guardedTick (parameterRules priority target trigger hit q.1) stop q.2) :=
  (freeze_measurable stop).comp ((tick_joint_measurable priority target trigger hit htrigger hhit).comp
    (measurable_fst.prodMk ((freeze_measurable stop).comp measurable_snd)))

include htrigger hhit in
theorem guardedRun_joint_measurable (stop : State L M ell → Bool) (n : ℕ) :
    Measurable (fun q : Ω × Phase L M ell X A =>
      guardedRun (parameterRules priority target trigger hit q.1) stop n q.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih => exact ih.comp (measurable_fst.prodMk
      (guardedTick_joint_measurable priority target trigger hit htrigger hhit stop))

end GradientHessian.ControllerMeasurable
