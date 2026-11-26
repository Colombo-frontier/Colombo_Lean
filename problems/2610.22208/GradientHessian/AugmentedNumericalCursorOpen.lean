import GradientHessian.AugmentedNumericalCursorInvariant
import GradientHessian.NumericalSupplySplit

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
  (stop : State L M ell → Bool) (hell : 0<ell)
  (hretire : ∀ s,Ready s → ∀ a,stop s=true → stop (retireNode s (R.target a))=true)
  (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)

include hell hretire hnormal in
theorem stop_persists (hi : Coherent stop initial) (N : ℕ) (q : Cursor L M ell S X A)
    (hq : coherent stop q) (hs : stop (state initial q)=true) :
    stop (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q))=true := by
  cases q with
  | inr q =>
      rw [run_active]
      exact ControllerDriverMonotonicity.stop_persists_run P R stop o v hell hretire hnormal q (hq q rfl) hs N
  | inl star =>
      cases N with
      | zero => exact hs
      | succ N =>
          rw [run_suspended_succ]
          exact ControllerDriverMonotonicity.stop_persists_run P R stop o v hell hretire hnormal initial hi hs N

include hell hretire hnormal in
theorem open_prefix (hinit : Coherent stop initial) (N i : ℕ) (hi : i≤N)
    (q : Cursor L M ell S X A) (hq : coherent stop q)
    (hN : stop (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q))=false) :
    stop (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q))=false := by
  cases hh : stop (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)) with
  | false => rfl
  | true =>
      have hp := stop_persists P R o v initial stop hell hretire hnormal hinit (N-i)
        (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)
        (run_coherent P R o v initial stop hell hnormal hinit i q hq) hh
      simp only [AugmentedNumericalCursorCounts.run,← Function.iterate_add_apply,Nat.sub_add_cancel hi] at hp
      change stop (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q))=true at hp
      rw [hN] at hp
      cases hp

include hell hretire hnormal in
theorem guarded_eq_of_open_endpoint (hi : Coherent stop initial) (N : ℕ) (q : Cursor L M ell S X A)
    (hq : coherent stop q)
    (hN : stop (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q))=false) :
    AugmentedNumericalCursorCounts.run P R stop o v initial N q=
      AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q := by
  cases q with
  | inr q =>
      rw [run_active] at hN
      rw [run_active,run_active]
      exact congrArg Sum.inr (ControllerDriverMonotonicity.guarded_eq_at_open_endpoint
        P R stop o v hell hretire hnormal q (hq q rfl) N hN)
  | inl star =>
      cases N with
      | zero => rfl
      | succ N =>
          rw [run_suspended_succ] at hN
          rw [run_suspended_succ,run_suspended_succ]
          exact congrArg Sum.inr (ControllerDriverMonotonicity.guarded_eq_at_open_endpoint
            P R stop o v hell hretire hnormal initial hi N hN)

def finished : Cursor L M ell S X A → Bool
  | .inl _ => false
  | .inr q => NumericalDriverInstructions.finished q

theorem unfinished_prefix (N i : ℕ) (hi : i≤N) (q : Cursor L M ell S X A)
    (hN : finished (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)=false) :
    finished (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)=false := by
  cases q with
  | inr q =>
      rw [run_active] at hN
      rw [run_active]
      exact NumericalSupplySplit.unfinished_prefix P R o v q N i hi hN
  | inl star =>
      cases i with
      | zero => rfl
      | succ i =>
          cases N with
          | zero => omega
          | succ N =>
              rw [run_suspended_succ] at hN
              rw [run_suspended_succ]
              exact NumericalSupplySplit.unfinished_prefix P R o v initial N i (by omega) hN

end GradientHessian.AugmentedNumericalCursorInvariant
