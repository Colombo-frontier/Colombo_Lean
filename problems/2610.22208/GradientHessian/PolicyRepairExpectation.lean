import GradientHessian.MachinePolicySchedule
import GradientHessian.ControllerRepairProbability

/-! Actual repair random variables for an arbitrary mixed policy and its
virtual output are measurable and integrable. The finite event-sum mean
bound uses the original parameter/seed space; stopped event estimates are
the remaining probabilistic input. -/

noncomputable section
namespace GradientHessian.PolicyRepairExpectation
open Classical MeasureTheory Machine TaskState TaskSlots ComparisonController
  ComparisonControllerLedger ControllerMeasurable ControllerRepairEvents
  ControllerRepairProbability

variable {Ω Seed S X Y Z A : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable {L M ell : ℕ}

variable (priority : List A) (target : A → FrontierState.Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a, Measurable (fun p : Ω × X => trigger p.1 s p.2 a))
  (hhit : ∀ s, Measurable (fun p : Ω × X => hit p.1 s p.2))
  (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z)
  (ho : Measurable (fun q : Ω × X => o q.1 q.2)) (hr : Measurable (fun q : Ω × X => r q.1 q.2))

def policyPoints (n : ℕ) (q : Ω × Seed) : List (Pending X) :=
  ControllerPolicyTrace.withOutput P (o q.1) (r q.1) n q.2

def policyRules (q : Ω × Seed) : Rules L M ell X A :=
  parameterRules priority target trigger hit q.1

include htrigger hhit ho hr in
theorem repair_measurable (n : ℕ) :
    Measurable (count (policyRules priority target trigger hit : Ω × Seed → _)
      (policyPoints P o r n) (fun _ => initial)) := by
  have ht (s : State L M ell) (a : A) :
      Measurable (fun q : (Ω × Seed) × X => trigger q.1.1 s q.2 a) :=
    (htrigger s a).comp (measurable_fst.fst.prodMk measurable_snd)
  have hh (s : State L M ell) :
      Measurable (fun q : (Ω × Seed) × X => hit q.1.1 s q.2) :=
    (hhit s).comp (measurable_fst.fst.prodMk measurable_snd)
  have hm := ControllerOptionalTrajectory.repair_tally_measurable priority target
    (fun q : Ω × Seed => trigger q.1) (fun q : Ω × Seed => hit q.1) ht hh
    (MachinePolicySchedule.withOutput P o r n)
    (MachinePolicySchedule.withOutput_measurable P o r ho hr n) (fun _ => initial) measurable_const
  simpa only [MachinePolicySchedule.withOutput_selected,policyPoints,policyRules,count,parameterRules] using hm

include htrigger hhit ho hr in
theorem repair_event_measurable (n : ℕ) (a : A) :
    MeasurableSet (event (policyRules priority target trigger hit : Ω × Seed → _)
      (policyPoints P o r n) (fun _ => initial) a) := by
  have ht (s : State L M ell) (a : A) :
      Measurable (fun q : (Ω × Seed) × X => trigger q.1.1 s q.2 a) :=
    (htrigger s a).comp (measurable_fst.fst.prodMk measurable_snd)
  have hh (s : State L M ell) :
      Measurable (fun q : (Ω × Seed) × X => hit q.1.1 s q.2) :=
    (hhit s).comp (measurable_fst.fst.prodMk measurable_snd)
  have hm := ControllerOptionalTrajectory.action_event_measurable priority target
    (fun q : Ω × Seed => trigger q.1) (fun q : Ω × Seed => hit q.1) ht hh
    (MachinePolicySchedule.withOutput P o r n)
    (MachinePolicySchedule.withOutput_measurable P o r ho hr n) (fun _ => initial) measurable_const a
  simpa only [MachinePolicySchedule.withOutput_selected,policyPoints,policyRules,event,parameterRules] using hm

include htrigger hhit ho hr in
theorem repair_integrable (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ] (n : ℕ) (hell : 0<ell) :
    Integrable (fun q => (count (policyRules priority target trigger hit : Ω × Seed → _)
      (policyPoints P o r n) (fun _ => initial) q : ℝ)) μ :=
  count_integrable μ (policyRules priority target trigger hit) (policyPoints P o r n)
    (fun _ => initial) (fun _ => initial_ready hell) hell
    (fun a => (FrontierState.subtree (target a)).card*M) (fun _ _ => le_rfl)
    (repair_measurable priority target trigger hit htrigger hhit P o r ho hr n)
    (repair_event_measurable priority target trigger hit htrigger hhit P o r ho hr n)

include htrigger hhit ho hr in
theorem mean_le_events (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ] (n : ℕ) (hell : 0<ell) :
    (∫ q, (count (policyRules priority target trigger hit : Ω × Seed → _)
      (policyPoints P o r n) (fun _ => initial) q : ℝ) ∂μ) ≤
      ∑ a : A, ((FrontierState.subtree (target a)).card*M : ℝ)*
        μ.real (event (policyRules priority target trigger hit) (policyPoints P o r n) (fun _ => initial) a) := by
  have hm := mean_le_event_sum μ (policyRules priority target trigger hit) (policyPoints P o r n)
    (fun _ => initial) (fun _ => initial_ready hell) hell
    (fun a => (FrontierState.subtree (target a)).card*M) (fun _ _ => le_rfl)
    (repair_measurable priority target trigger hit htrigger hhit P o r ho hr n)
    (repair_event_measurable priority target trigger hit htrigger hhit P o r ho hr n)
  simpa only [Nat.cast_mul] using hm

end GradientHessian.PolicyRepairExpectation
