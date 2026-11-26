import GradientHessian.AugmentedNumericalCursorCounts

noncomputable section
namespace GradientHessian.AugmentedNumericalCursorInvariant
open Classical FrontierState TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerDriverMonotonicity ControllerDriverResource AugmentedNumericalCursorCounts

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)
  (initial : Config L M ell S X A)

def coherent (stop : State L M ell → Bool) (q : Cursor L M ell S X A) : Prop :=
  ∀ a,q=Sum.inr a → Coherent stop a

theorem run_ready (stop : State L M ell → Bool) (hell : 0<ell)
    (N : ℕ) (q : Cursor L M ell S X A) (hq : Ready (state initial q)) :
    Ready (state initial (AugmentedNumericalCursorCounts.run P R stop o v initial N q)) := by
  cases q with
  | inr q =>
      rw [run_active]
      exact ControllerDriverResource.run_good P R stop o v hell q hq N
  | inl star =>
      cases N with
      | zero => exact hq
      | succ N =>
          rw [run_suspended_succ]
          exact ControllerDriverResource.run_good P R stop o v hell initial hq N

theorem run_coherent (stop : State L M ell → Bool) (hell : 0<ell)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (hi : Coherent stop initial) (N : ℕ) (q : Cursor L M ell S X A) (hq : coherent stop q) :
    coherent stop (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q) := by
  cases q with
  | inr q =>
      rw [run_active]
      intro a ha
      cases ha
      exact ControllerDriverMonotonicity.run_coherent P R stop o v hell hnormal q (hq q rfl) N
  | inl star =>
      cases N with
      | zero => exact hq
      | succ N =>
          rw [run_suspended_succ]
          intro a ha
          cases ha
          exact ControllerDriverMonotonicity.run_coherent P R stop o v hell hnormal initial hi N

end GradientHessian.AugmentedNumericalCursorInvariant
