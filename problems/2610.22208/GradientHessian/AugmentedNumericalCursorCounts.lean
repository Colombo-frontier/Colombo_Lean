import GradientHessian.ControllerPostWindow

/-! Suspending initialization adds one free transition and no query or
selection. These are counts of the literal chronological driver after the
policy has received its initial public packet. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalCursorCounts
open Classical FrontierState TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerDriverMonotonicity ControllerDriverResource

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

abbrev Cursor (L M ell : ℕ) (S X A : Type*) := PUnit ⊕ Config L M ell S X A

variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (stop : State L M ell → Bool)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)
  (initial : Config L M ell S X A)

def step : Cursor L M ell S X A → Cursor L M ell S X A
  | .inl _ => .inr initial
  | .inr q => .inr (ControllerPolicyDriver.step P R stop o v q)

def run (N : ℕ) (q : Cursor L M ell S X A) : Cursor L M ell S X A :=
  (step P R stop o v initial)^[N] q

def state : Cursor L M ell S X A → State L M ell
  | .inl _ => stateOf initial
  | .inr q => stateOf q

def lift (test : Config L M ell S X A → ℕ) : Cursor L M ell S X A → ℕ
  | .inl _ => 0
  | .inr q => test q

theorem run_active (N : ℕ) (q : Config L M ell S X A) :
    run P R stop o v initial N (.inr q)=.inr (ControllerPolicyDriver.run P R stop o v N q) := by
  induction N generalizing q with
  | zero => rfl
  | succ N ih =>
      rw [run,Function.iterate_succ_apply]
      exact ih _

theorem run_suspended_succ (N : ℕ) (star : PUnit) :
    run P R stop o v initial (N+1) (.inl star)=
      .inr (ControllerPolicyDriver.run P R stop o v N initial) := by
  rw [run,Function.iterate_succ_apply]
  exact run_active P R stop o v initial N initial

def count (test : Config L M ell S X A → ℕ) (N : ℕ) (q : Cursor L M ell S X A) : ℕ :=
  ∑ i∈Finset.range N,lift test (run P R stop o v initial i q)

theorem count_active (test : Config L M ell S X A → ℕ) (N : ℕ) (q : Config L M ell S X A) :
    count P R stop o v initial test N (.inr q)=
      ControllerDriverResource.count P R stop o v test N q := by
  simp only [count,run_active,lift,ControllerDriverResource.count_eq_sum]

theorem count_suspended_succ (test : Config L M ell S X A → ℕ) (N : ℕ) (star : PUnit) :
    count P R stop o v initial test (N+1) (.inl star)=
      ControllerDriverResource.count P R stop o v test N initial := by
  rw [count,Finset.sum_range_succ']
  simp_rw [run_suspended_succ]
  simp only [lift,run,Function.iterate_zero,Function.id_def,Nat.add_zero,
    ControllerDriverResource.count_eq_sum]

theorem product_bound (hell : 0<ell) (leaf : Leaf L) (N : ℕ) (q : Cursor L M ell S X A)
    (hq : Ready (state initial q)) :
    count P R stop o v initial
      (fun q => if NumericalDriverInstructions.product leaf stop q then 1 else 0) N q≤M*ell+1 := by
  cases q with
  | inr q =>
      rw [count_active,ControllerDriverResource.count_eq_sum]
      exact actual_product_bound P R stop o v hell leaf N q hq
  | inl star =>
      cases N with
      | zero => simp [count]
      | succ N =>
          rw [count_suspended_succ,ControllerDriverResource.count_eq_sum]
          exact actual_product_bound P R stop o v hell leaf N initial hq

theorem post_product_bound (hell : 0<ell) (leaf : Leaf L) (j : Fin M)
    (N : ℕ) (q : Cursor L M ell S X A) (hq : Ready (state initial q))
    (hcur : TaskState.current (state initial q)=some leaf)
    (hindex : ((state initial q).completed leaf).val=j.val) :
    count P R (taskDisclosed leaf j) o v initial
      (fun q => if NumericalDriverInstructions.product leaf (taskDisclosed leaf j) q then 1 else 0) N q≤ell+1 := by
  cases q with
  | inr q =>
      rw [count_active,ControllerDriverResource.count_eq_sum]
      exact ControllerDriverResource.post_product_bound P R o v hell leaf j q hq hcur hindex N
  | inl star =>
      cases N with
      | zero => simp [count]
      | succ N =>
          rw [count_suspended_succ,ControllerDriverResource.count_eq_sum]
          exact ControllerDriverResource.post_product_bound P R o v hell leaf j initial hq hcur hindex N

theorem post_normal_bound (hell : 0<ell) (leaf : Leaf L) (j : Fin M)
    (N : ℕ) (q : Cursor L M ell S X A) (hq : Ready (state initial q))
    (hcur : TaskState.current (state initial q)=some leaf)
    (hindex : ((state initial q).completed leaf).val=j.val) :
    count P R (taskDisclosed leaf j) o v initial
      (normalBit (fun _ => true) (taskDisclosed leaf j)) N q≤ell := by
  cases q with
  | inr q =>
      rw [count_active]
      exact (ControllerDriverResource.post_normal_bound P R o v hell leaf j q hq hcur hindex N).1
  | inl star =>
      cases N with
      | zero => simp [count]
      | succ N =>
          rw [count_suspended_succ]
          exact (ControllerDriverResource.post_normal_bound P R o v hell leaf j initial hq hcur hindex N).1

end GradientHessian.AugmentedNumericalCursorCounts

