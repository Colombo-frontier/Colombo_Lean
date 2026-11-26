import GradientHessian.ControllerPolicyDriver
import GradientHessian.ControllerMeasurablePhases

/-! The chronological driver's measurable state retains the original
sigma algebras on private policy state and physical points. Only finite
controller counters and modes are discrete. -/

noncomputable section
namespace GradientHessian.ControllerPolicyDriver
open Classical TaskState ComparisonController ComparisonControllerReplay ControllerMeasurable

variable {L M ell : ℕ} {Ω Seed S X Y Z A T : Type*}

abbrev ReadyData (L M ell : ℕ) (S : Type*) := ℕ × S × State L M ell
abbrev PendingData (L M ell : ℕ) (S X A : Type*) := ℕ × S × Bool × Phase L M ell X A
abbrev Encoded (L M ell : ℕ) (S X A : Type*) :=
  ReadyData L M ell S ⊕ PendingData L M ell S X A ⊕ (S × State L M ell)

def configEquiv (L M ell : ℕ) (S X A : Type*) : Config L M ell S X A ≃ Encoded L M ell S X A where
  toFun q := match q with
    | .ready n a s => .inl (n,a,s)
    | .pending n a output phase => .inr (.inl (n,a,output,phase))
    | .finished a s => .inr (.inr (a,s))
  invFun q := match q with
    | .inl (n,a,s) => .ready n a s
    | .inr (.inl (n,a,output,phase)) => .pending n a output phase
    | .inr (.inr (a,s)) => .finished a s
  left_inv q := by cases q <;> rfl
  right_inv q := by rcases q with q | q | q <;> rfl

variable [MeasurableSpace S] [MeasurableSpace X]

instance configMeasurable : MeasurableSpace (Config L M ell S X A) :=
  MeasurableSpace.comap (configEquiv L M ell S X A) inferInstance

def configMeasurableEquiv (L M ell : ℕ) (S X A : Type*) [MeasurableSpace S] [MeasurableSpace X] :
    Config L M ell S X A ≃ᵐ Encoded L M ell S X A := transportEquiv (configEquiv L M ell S X A)

variable [MeasurableSpace Ω] [MeasurableSpace T]

theorem measurable_ready {n : T → ℕ} {a : T → S} {s : T → State L M ell}
    (hn : Measurable n) (ha : Measurable a) (hs : Measurable s) :
    Measurable (fun q => Config.ready (X := X) (Action := A) (n q) (a q) (s q)) :=
  (configMeasurableEquiv L M ell S X A).symm.measurable.comp
    (measurable_inl.comp (hn.prodMk (ha.prodMk hs)))

theorem measurable_pending {n : T → ℕ} {a : T → S} {output : T → Bool}
    {phase : T → Phase L M ell X A}
    (hn : Measurable n) (ha : Measurable a) (ho : Measurable output) (hp : Measurable phase) :
    Measurable (fun q => Config.pending (n q) (a q) (output q) (phase q)) :=
  (configMeasurableEquiv L M ell S X A).symm.measurable.comp
    (measurable_inr.comp (measurable_inl.comp (hn.prodMk (ha.prodMk (ho.prodMk hp)))))

theorem measurable_finished {a : T → S} {s : T → State L M ell}
    (ha : Measurable a) (hs : Measurable s) :
    Measurable (fun q => Config.finished (X := X) (Action := A) (a q) (s q)) :=
  (configMeasurableEquiv L M ell S X A).symm.measurable.comp
    (measurable_inr.comp (measurable_inr.comp (ha.prodMk hs)))

theorem measurable_config_cases (f : Ω → Config L M ell S X A → T)
    (hr : Measurable (fun q : Ω × ReadyData L M ell S => f q.1 (.ready q.2.1 q.2.2.1 q.2.2.2)))
    (hp : Measurable (fun q : Ω × PendingData L M ell S X A =>
      f q.1 (.pending q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)))
    (hf : Measurable (fun q : Ω × (S × State L M ell) => f q.1 (.finished q.2.1 q.2.2))) :
    Measurable (fun q : Ω × Config L M ell S X A => f q.1 q.2) := by
  have hright : Measurable (fun q : Ω × (PendingData L M ell S X A ⊕ (S × State L M ell)) =>
      f q.1 ((configEquiv L M ell S X A).symm (.inr q.2))) := by
    let g : (Ω × PendingData L M ell S X A) ⊕ (Ω × (S × State L M ell)) → T :=
      Sum.elim (fun q => f q.1 (.pending q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
        (fun q => f q.1 (.finished q.2.1 q.2.2))
    have hg : Measurable g := measurable_sum hp hf
    convert hg.comp (MeasurableEquiv.prodSumDistrib Ω (PendingData L M ell S X A) (S × State L M ell)).measurable using 1
    funext q
    rcases q with ⟨w,p|p⟩ <;> rfl
  have hsum : Measurable (fun q : Ω × Encoded L M ell S X A =>
      f q.1 ((configEquiv L M ell S X A).symm q.2)) := by
    let g : (Ω × ReadyData L M ell S) ⊕ (Ω × (PendingData L M ell S X A ⊕ (S × State L M ell))) → T :=
      Sum.elim (fun q => f q.1 (.ready q.2.1 q.2.2.1 q.2.2.2))
        (fun q => f q.1 ((configEquiv L M ell S X A).symm (.inr q.2)))
    have hg : Measurable g := measurable_sum hr hright
    convert hg.comp (MeasurableEquiv.prodSumDistrib Ω (ReadyData L M ell S)
      (PendingData L M ell S X A ⊕ (S × State L M ell))).measurable using 1
    funext q
    rcases q with ⟨w,p|p⟩ <;> rfl
  convert hsum.comp
    (measurable_fst.prodMk ((configMeasurableEquiv L M ell S X A).measurable.comp measurable_snd)) using 1
  funext q
  rcases q with ⟨w,q⟩
  cases q <;> rfl

variable [MeasurableSpace Seed] [MeasurableSpace Y] [MeasurableSpace Z]
variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable (P : Machine.Policy Seed S X Y Z) (R : Ω → Rules L M ell X A)
  (stop : State L M ell → Bool)
  (ordinary : Ω → State L M ell → State L M ell → X → Y)
  (rich : Ω → State L M ell → State L M ell → X → Z)

theorem ready_step_measurable :
    Measurable (fun q : Ω × ReadyData L M ell S =>
      step P (R q.1) stop (ordinary q.1) (rich q.1) (.ready q.2.1 q.2.2.1 q.2.2.2)) := by
  have hfixed : Measurable (fun q : (Ω × S) × (ℕ × State L M ell) =>
      step P (R q.1.1) stop (ordinary q.1.1) (rich q.1.1) (.ready q.2.1 q.1.2 q.2.2)) := by
    apply measurable_from_prod_countable
    rintro ⟨n,s⟩
    have hmode : Measurable (fun q : Ω × S => P.mode q.2) := P.mode_measurable.comp measurable_snd
    have hout : Measurable (fun q : Ω × S => Config.pending (Action := A) n q.2 true
        (.repairing ⟨P.output q.2,.ordinary⟩ s)) :=
      measurable_pending measurable_const measurable_snd measurable_const
        (measurable_phase_decode (measurable_pending_mk (P.output_measurable.comp measurable_snd) measurable_const)
          (measurable_const (a := (.inl s : PhaseData L M ell))))
    have hquery : Measurable (fun q : Ω × S => Config.pending (Action := A) n q.2 false
        (.repairing ⟨P.point q.2,if P.mode q.2=2 then .ordinary else .rich⟩ s)) :=
      measurable_pending measurable_const measurable_snd measurable_const
        (measurable_phase_decode (measurable_pending_mk (P.point_measurable.comp measurable_snd)
          (Measurable.ite (hmode (measurableSet_singleton 2)) measurable_const measurable_const))
          (measurable_const (a := (.inl s : PhaseData L M ell))))
    cases hs : stop s with
    | true => simpa only [step,hs,if_true] using
        (measurable_finished (X := X) (A := A) measurable_snd (measurable_const (a := s)) :
          Measurable (fun q : Ω × S => Config.finished q.2 s))
    | false =>
      by_cases hn : n=0
      · simpa only [step,hs,Bool.false_eq_true,if_false,hn,true_or,if_true] using hout
      · simp only [step,hs,Bool.false_eq_true,if_false,hn,false_or]
        exact Measurable.ite (hmode (measurableSet_singleton 0)) hout
          (Measurable.ite (hmode (measurableSet_singleton 1))
            (measurable_ready measurable_const (P.think_measurable.comp measurable_snd) measurable_const) hquery)
  exact hfixed.comp ((measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
    ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))

variable
  (hguard : Measurable (fun q : Ω × Phase L M ell X A => guardedTick (R q.1) stop q.2))
  (ho : ∀ b a,Measurable (fun q : Ω × X => ordinary q.1 b a q.2))
  (hr : ∀ b a,Measurable (fun q : Ω × X => rich q.1 b a q.2))

include hguard ho hr in
theorem pending_step_measurable :
    Measurable (fun q : Ω × PendingData L M ell S X A =>
      step P (R q.1) stop (ordinary q.1) (rich q.1)
        (.pending q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) := by
  have hfixed : Measurable (fun q : (Ω × S × X) × (ℕ × Bool × Kind × PhaseData L M ell) =>
      step P (R q.1.1) stop (ordinary q.1.1) (rich q.1.1)
        (.pending q.2.1 q.1.2.1 q.2.2.1
          ((phaseEquiv L M ell X A).symm (⟨q.1.2.2,q.2.2.2.1⟩,q.2.2.2.2)))) := by
    apply measurable_from_prod_countable
    rintro ⟨n,output,kind,data⟩
    have ha : Measurable (fun q : Ω × S × X => q.2.1) := measurable_fst.comp measurable_snd
    have hx : Measurable (fun q : Ω × S × X => q.2.2) := measurable_snd.comp measurable_snd
    have hp : Measurable (fun q : Ω × S × X => Pending.mk q.2.2 kind) :=
      measurable_pending_mk hx measurable_const
    have hphase : Measurable (fun q : Ω × S × X => (phaseEquiv L M ell X A).symm (⟨q.2.2,kind⟩,data)) :=
      measurable_phase_decode hp measurable_const
    have hg := hguard.comp (measurable_fst.prodMk hphase)
    rcases data with s | s | ⟨before,after⟩ | s
    · exact measurable_pending measurable_const ha measurable_const hg
    · exact measurable_pending measurable_const ha measurable_const hg
    · change Measurable (fun q : Ω × S × X =>
        deliver P stop (ordinary q.1) (rich q.1) n q.2.1 output ⟨q.2.2,kind⟩ before after)
      cases hb : stop before <;> cases he : stop after <;> cases output <;> cases kind <;>
        simp only [deliver,hb,he,Bool.or_false,Bool.or_true,Bool.false_eq_true,if_false,if_true]
      · exact measurable_ready measurable_const (P.ordinaryNext_measurable.comp
          (ha.prodMk ((ho before after).comp (measurable_fst.prodMk hx)))) measurable_const
      · exact measurable_ready measurable_const (P.richNext_measurable.comp
          (ha.prodMk ((hr before after).comp (measurable_fst.prodMk hx)))) measurable_const
      all_goals exact measurable_finished ha measurable_const
    · exact measurable_finished ha measurable_const
  have hphase : Measurable (fun q : Ω × PendingData L M ell S X A =>
      (phaseEquiv L M ell X A) q.2.2.2.2) :=
    (phaseMeasurableEquiv L M ell X A).measurable.comp (by fun_prop)
  have hp := measurable_fst.comp hphase
  have h := hfixed.comp
    ((measurable_fst.prodMk ((by fun_prop : Measurable (fun q : Ω × PendingData L M ell S X A => q.2.2.1)).prodMk
      (measurable_pending_point.comp hp))).prodMk
      ((by fun_prop : Measurable (fun q : Ω × PendingData L M ell S X A => q.2.1)).prodMk
        ((by fun_prop : Measurable (fun q : Ω × PendingData L M ell S X A => q.2.2.2.1)).prodMk
          ((measurable_pending_kind.comp hp).prodMk (measurable_snd.comp hphase)))))
  convert h using 1
  funext q
  rcases q with ⟨w,n,a,output,phase⟩
  cases phase <;> rfl

include hguard ho hr in
theorem step_joint_measurable :
    Measurable (fun q : Ω × Config L M ell S X A => step P (R q.1) stop (ordinary q.1) (rich q.1) q.2) := by
  apply measurable_config_cases (fun w q => step P (R w) stop (ordinary w) (rich w) q)
  · exact ready_step_measurable P R stop ordinary rich
  · exact pending_step_measurable P R stop ordinary rich hguard ho hr
  · exact measurable_finished (by fun_prop) (by fun_prop)

include hguard ho hr in
theorem run_joint_measurable (fuel : ℕ) :
    Measurable (fun q : Ω × Config L M ell S X A => run P (R q.1) stop (ordinary q.1) (rich q.1) fuel q.2) := by
  induction fuel with
  | zero => exact measurable_snd
  | succ fuel ih => exact ih.comp (measurable_fst.prodMk (step_joint_measurable P R stop ordinary rich hguard ho hr))

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem initial_measurable (N : ℕ) (s : State L M ell) :
    Measurable (initial (X := X) (Action := A) P N · s) :=
  measurable_ready measurable_const P.initial_measurable measurable_const

end GradientHessian.ControllerPolicyDriver
