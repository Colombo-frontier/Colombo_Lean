import GradientHessian.ControllerEarlyEvents

/-! The actual early count is exactly the sum of its task-event probabilities.
All measurability is derived along the original policy and virtual output. -/

noncomputable section
namespace GradientHessian.PolicyEarlyExpectation
open Classical MeasureTheory Machine TaskState TaskSlots ComparisonController
  ComparisonControllerLedger ControllerMeasurable PolicyRepairExpectation
open scoped BigOperators

variable {Ω Seed S X Y Z A : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable {L M ell : ℕ}

variable (priority : List A) (target : A → FrontierState.Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a, Measurable (fun p : Ω × X => trigger p.1 s p.2 a))
  (hhit : ∀ s, Measurable (fun p : Ω × X => hit p.1 s p.2))

include htrigger hhit in
theorem earlyFor_along_measurable (p : Ω → Pending X) (hp : Measurable p)
    (s : Ω → State L M ell) (hs : Measurable s) (q : ControllerEarlyEvents.Task L M) :
    Measurable (fun w => ControllerEarlyEvents.earlyFor
      (parameterRules priority target trigger hit w) (p w) (s w) q) := by
  classical
  have hb := measurable_receipt_beforeNormal.comp
    (serve_along_measurable priority target trigger hit htrigger hhit p hp s hs)
  have hpick := (measurable_of_countable (fun u : State L M ell =>
    decide (TaskState.current u=some q.1 ∧ (u.completed q.1).val=q.2.val))).comp hb
  have he := PolicyEarlyIntegrability.early_along_measurable
    priority target trigger hit htrigger hhit p hp s hs
  have hcond : MeasurableSet {w | TaskState.current
      (serve (parameterRules priority target trigger hit w) (p w) (s w)).beforeNormal=some q.1 ∧
      ((serve (parameterRules priority target trigger hit w) (p w) (s w)).beforeNormal.completed q.1).val=q.2.val} := by
    convert hpick (measurableSet_singleton true) using 1
    ext w
    simp only [Set.mem_preimage,Set.mem_singleton_iff,decide_eq_true_eq,
      Function.comp_apply,Set.mem_setOf_eq]
  exact Measurable.ite hcond he measurable_const

variable (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z)
  (ho : Measurable (fun q : Ω × X => o q.1 q.2)) (hr : Measurable (fun q : Ω × X => r q.1 q.2))

def taskCount (n : ℕ) (q : ControllerEarlyEvents.Task L M) (w : Ω × Seed) : ℕ :=
  ControllerEarlyEvents.count (policyRules priority target trigger hit w)
    (policyPoints P o r n w) initial q

def event (n : ℕ) (q : ControllerEarlyEvents.Task L M) : Set (Ω × Seed) :=
  {w | 0<taskCount priority target trigger hit P o r n q w}

include htrigger hhit ho hr in
theorem taskCount_measurable (n : ℕ) (q : ControllerEarlyEvents.Task L M) :
    Measurable (taskCount priority target trigger hit P o r n q) := by
  have ht (s : State L M ell) (a : A) :
      Measurable (fun q : (Ω × Seed) × X => trigger q.1.1 s q.2 a) :=
    (htrigger s a).comp (measurable_fst.fst.prodMk measurable_snd)
  have hh (s : State L M ell) :
      Measurable (fun q : (Ω × Seed) × X => hit q.1.1 s q.2) :=
    (hhit s).comp (measurable_fst.fst.prodMk measurable_snd)
  have hm := ControllerOptionalTrajectory.tally_measurable priority target
    (fun w : Ω × Seed => trigger w.1) (fun w : Ω × Seed => hit w.1) ht hh
    (fun w p s => ControllerEarlyEvents.earlyFor (policyRules priority target trigger hit w) p s q)
    (fun p hp s hs => earlyFor_along_measurable priority target
      (fun w : Ω × Seed => trigger w.1) (fun w : Ω × Seed => hit w.1) ht hh p hp s hs q)
    (MachinePolicySchedule.withOutput P o r n)
    (MachinePolicySchedule.withOutput_measurable P o r ho hr n) (fun _ => initial) measurable_const
  simpa only [MachinePolicySchedule.withOutput_selected,taskCount,ControllerEarlyEvents.count,
    policyPoints,policyRules] using hm

include htrigger hhit ho hr in
theorem event_measurable (n : ℕ) (q : ControllerEarlyEvents.Task L M) :
    MeasurableSet (event priority target trigger hit P o r n q) :=
  measurableSet_lt measurable_const
    (taskCount_measurable priority target trigger hit htrigger hhit P o r ho hr n q)

include htrigger hhit ho hr in
theorem mean_eq_probability_sum (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ]
    (n : ℕ) (hell : 0<ell) :
    (∫ w, (PolicyEarlyIntegrability.count priority target trigger hit P o r n w:ℝ) ∂μ) =
      ∑ q : ControllerEarlyEvents.Task L M, μ.real (event priority target trigger hit P o r n q) := by
  have hi (q : ControllerEarlyEvents.Task L M) :
      Integrable ((event priority target trigger hit P o r n q).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const _).indicator (event_measurable priority target trigger hit htrigger hhit P o r ho hr n q)
  calc
    _ = ∫ w, ∑ q : ControllerEarlyEvents.Task L M,
        (event priority target trigger hit P o r n q).indicator (fun _ => (1:ℝ)) w ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      have he := ControllerEarlyEvents.early_eq_event_sum
        (policyRules priority target trigger hit w) (policyPoints P o r n w) (initial_ready hell) hell
      have he' := congrArg (fun k : ℕ => (k:ℝ)) he
      simpa only [PolicyEarlyIntegrability.count,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,
        Nat.cast_zero,event,Set.indicator_apply,Set.mem_setOf_eq,taskCount] using he'
    _ = _ := by
      rw [integral_finset_sum Finset.univ (fun q _ => hi q)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_indicator_const _ (event_measurable priority target trigger hit htrigger hhit P o r ho hr n q)]
      simp

include htrigger hhit ho hr in
theorem mean_le_probability_bounds (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ]
    (n : ℕ) (hell : 0<ell) (bound : ControllerEarlyEvents.Task L M → ℝ)
    (hp : ∀ q, μ.real (event priority target trigger hit P o r n q)≤bound q) :
    (∫ w, (PolicyEarlyIntegrability.count priority target trigger hit P o r n w:ℝ) ∂μ) ≤
      ∑ q : ControllerEarlyEvents.Task L M, bound q := by
  rw [mean_eq_probability_sum priority target trigger hit htrigger hhit P o r ho hr μ n hell]
  exact Finset.sum_le_sum (fun q _ => hp q)

include htrigger hhit ho hr in
theorem mean_le_inventory_fraction (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ]
    (n : ℕ) (hell : 0<ell)
    (hp : ∀ q, μ.real (event priority target trigger hit P o r n q)≤1/256) :
    (∫ w, (PolicyEarlyIntegrability.count priority target trigger hit P o r n w:ℝ) ∂μ) ≤
      (8:ℝ)^L*M/256 := by
  have hm := mean_le_probability_bounds priority target trigger hit htrigger hhit
    P o r ho hr μ n hell (fun _ => 1/256) hp
  simpa only [Finset.sum_const,Finset.card_univ,ControllerEarlyEvents.Task,
    Fintype.card_prod,FrontierState.leaf_card,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_one_div] using hm

end GradientHessian.PolicyEarlyExpectation
