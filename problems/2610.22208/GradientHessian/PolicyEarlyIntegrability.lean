import GradientHessian.PolicyRepairExpectation

/-! Actual normal-early counts along the original policy trajectory are
measurable, bounded by the finite task inventory, and integrable. -/

noncomputable section
namespace GradientHessian.PolicyEarlyIntegrability
open Classical MeasureTheory Machine TaskState TaskSlots ComparisonController
  ComparisonControllerLedger ControllerMeasurable PolicyRepairExpectation

theorem serve_early_le_completed {L M ell : ℕ} {X A : Type*}
    (R : Rules L M ell X A) (p : Pending X) {s : State L M ell} (hs : Ready s) :
    completedTotal s+early R p s ≤ completedTotal (serve R p s).afterNormal := by
  have he := normal_completed_exact R p (repairRun_ready R p (8^L) hs)
  rw [repairCharge_exact] at he
  change completedTotal s+earlyCost R p (repairRun R p (8^L) s).1 ≤
    completedTotal (normal R p (repairRun R p (8^L) s).1)
  omega

theorem tally_early_le_completed {L M ell : ℕ} {X A : Type*}
    (R : Rules L M ell X A) (ps : List (Pending X)) {s : State L M ell}
    (hs : Ready s) (hell : 0<ell) :
    completedTotal s+tally R (early R) ps s ≤ completedTotal (VisibilityWindow.run R ps s) := by
  induction ps generalizing s with
  | nil => simp [tally,VisibilityWindow.run]
  | cons p ps ih =>
    have hp := serve_early_le_completed R p hs
    have ht := ih (serve_ready R p hs hell)
    simp only [tally,VisibilityWindow.run]
    omega

theorem tally_early_bound {L M ell : ℕ} {X A : Type*}
    (R : Rules L M ell X A) (ps : List (Pending X)) {s : State L M ell}
    (hs : Ready s) (hell : 0<ell) : tally R (early R) ps s ≤ 8^L*M := by
  have hb := tally_early_le_completed R ps hs hell
  have ht := completedTotal_le (VisibilityWindow.run R ps s)
  omega

variable {Ω Seed S X Y Z A : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable {L M ell : ℕ}

variable (priority : List A) (target : A → FrontierState.Node L)
  (trigger : Ω → State L M ell → X → A → Bool) (hit : Ω → State L M ell → X → Bool)
  (htrigger : ∀ s a, Measurable (fun p : Ω × X => trigger p.1 s p.2 a))
  (hhit : ∀ s, Measurable (fun p : Ω × X => hit p.1 s p.2))

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
include hhit in
theorem earlyCost_fixed_measurable (s : State L M ell) :
    Measurable (fun q : Ω × Pending X => earlyCost (parameterRules priority target trigger hit q.1) q.2 s) := by
  have hh := (hhit s).comp (measurable_fst.prodMk (measurable_pending_point.comp measurable_snd))
  have hk := measurable_pending_kind.comp (measurable_snd : Measurable (Prod.snd : Ω × Pending X → Pending X))
  exact (measurable_of_countable (fun q : Kind × Bool => match q.1,TaskState.current s with
    | .ordinary,some leaf => if q.2=true ∧ (s.slots leaf).val+1<ell then (1:ℕ) else 0
    | _,_ => 0)).comp (hk.prodMk hh)

include htrigger hhit in
theorem early_along_measurable (p : Ω → Pending X) (hp : Measurable p)
    (s : Ω → State L M ell) (hs : Measurable s) :
    Measurable (fun w => early (parameterRules priority target trigger hit w) (p w) (s w)) := by
  have he : Measurable (fun q : (Ω × Pending X) × State L M ell =>
      earlyCost (parameterRules priority target trigger hit q.1.1) q.1.2 q.2) :=
    measurable_from_prod_countable (earlyCost_fixed_measurable priority target trigger hit hhit)
  have hb := measurable_receipt_beforeNormal.comp
    (serve_along_measurable priority target trigger hit htrigger hhit p hp s hs)
  exact he.comp ((measurable_id.prodMk hp).prodMk hb)

variable (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z)
  (ho : Measurable (fun q : Ω × X => o q.1 q.2)) (hr : Measurable (fun q : Ω × X => r q.1 q.2))

def count (n : ℕ) (q : Ω × Seed) : ℕ :=
  tally (policyRules priority target trigger hit q) (early (policyRules priority target trigger hit q))
    (policyPoints P o r n q) initial

include htrigger hhit ho hr in
theorem early_measurable (n : ℕ) : Measurable (count priority target trigger hit P o r n) := by
  have ht (s : State L M ell) (a : A) :
      Measurable (fun q : (Ω × Seed) × X => trigger q.1.1 s q.2 a) :=
    (htrigger s a).comp (measurable_fst.fst.prodMk measurable_snd)
  have hh (s : State L M ell) :
      Measurable (fun q : (Ω × Seed) × X => hit q.1.1 s q.2) :=
    (hhit s).comp (measurable_fst.fst.prodMk measurable_snd)
  have hm := ControllerOptionalTrajectory.tally_measurable priority target
    (fun q : Ω × Seed => trigger q.1) (fun q : Ω × Seed => hit q.1) ht hh
    (fun q => early (policyRules priority target trigger hit q))
    (early_along_measurable priority target (fun q : Ω × Seed => trigger q.1)
      (fun q : Ω × Seed => hit q.1) ht hh)
    (MachinePolicySchedule.withOutput P o r n)
    (MachinePolicySchedule.withOutput_measurable P o r ho hr n) (fun _ => initial) measurable_const
  simpa only [MachinePolicySchedule.withOutput_selected,count,policyPoints,policyRules] using hm

include htrigger hhit ho hr in
theorem early_integrable (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ] (n : ℕ) (hell : 0<ell) :
    Integrable (fun q => (count priority target trigger hit P o r n q : ℝ)) μ := by
  apply (integrable_const ((8^L*M:ℕ):ℝ)).mono'
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      (early_measurable priority target trigger hit htrigger hhit P o r ho hr n)).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  change (count priority target trigger hit P o r n q:ℝ) ≤ ((8^L*M:ℕ):ℝ)
  exact_mod_cast (show count priority target trigger hit P o r n q ≤ 8^L*M from
    tally_early_bound (policyRules priority target trigger hit q)
      (policyPoints P o r n q) (initial_ready hell) hell)

end GradientHessian.PolicyEarlyIntegrability
