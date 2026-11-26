import GradientHessian.AugmentedNumericalCursorCounts
import GradientHessian.NumericalSupplySplit
import GradientHessian.AugmentedDisclosureStops

/-! First literal mark supply on the suspended policy cursor.  The split
retains the suspended initializer or the entire pending receipt verbatim. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalSupplySplit
open Classical FrontierState TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerDriverMonotonicity ControllerDriverResource
  AugmentedNumericalCursorCounts

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)
  (initial : Config L M ell S X A)

def finished : Cursor L M ell S X A → Bool
  | .inl _ => false
  | .inr q => NumericalDriverInstructions.finished q

def halt (leaf : Leaf L) (j : Fin M) (q : Cursor L M ell S X A) : Bool :=
  finished q || AugmentedDisclosure.markStop leaf j (state initial q)

theorem run_ready (hell : 0<ell) (q : Cursor L M ell S X A)
    (hq : Ready (state initial q)) (N : ℕ) :
    Ready (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)) := by
  cases q with
  | inr q =>
      rw [run_active]
      exact run_good P R (fun _ => false) o v hell q hq N
  | inl star =>
      cases N with
      | zero => exact hq
      | succ N =>
          rw [run_suspended_succ]
          exact run_good P R (fun _ => false) o v hell initial hq N

theorem unfinished_prefix (q : Cursor L M ell S X A) (N i : ℕ) (hi : i≤N)
    (hN : finished (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)=false) :
    finished (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)=false := by
  cases q with
  | inr q =>
      simp only [run_active,finished] at hN ⊢
      exact NumericalSupplySplit.unfinished_prefix P R o v q N i hi hN
  | inl star =>
      cases i with
      | zero => rfl
      | succ i =>
          cases N with
          | zero => omega
          | succ N =>
              simp only [run_suspended_succ,finished] at hN ⊢
              exact NumericalSupplySplit.unfinished_prefix P R o v initial N i (by omega) hN

theorem completed_prefix (hell : 0<ell) (q : Cursor L M ell S X A)
    (hq : Ready (state initial q)) (N i : ℕ) (hi : i≤N) (leaf : Leaf L) :
    ((state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)).completed leaf).val≤
      ((state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)).completed leaf).val := by
  cases q with
  | inr q =>
      simp only [run_active,state] at hq ⊢
      exact NumericalSupplySplit.completed_prefix P R o v hell q hq N i hi leaf
  | inl star =>
      cases N with
      | zero =>
          have he : i=0 := by omega
          subst i
          exact le_refl _
      | succ N =>
          rw [run_suspended_succ]
          cases i with
          | zero =>
              exact run_completed_mono P R (fun _ => false) o v hell initial hq N leaf
          | succ i =>
              rw [run_suspended_succ]
              exact NumericalSupplySplit.completed_prefix P R o v hell initial hq N i (by omega) leaf

theorem supplied_prefix_index (hell : 0<ell) (q : Cursor L M ell S X A)
    (hq : Ready (state initial q)) (leaf : Leaf L) (j : Fin M)
    (N i : ℕ) (hi : i≤N)
    (hend : ((state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)).completed leaf).val=j.val)
    (hs : AugmentedDisclosure.markStop leaf j
      (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q))=true) :
    TaskState.current (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q))=some leaf ∧
      ((state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)).completed leaf).val=j.val := by
  have hm := completed_prefix P R o v initial hell q hq N i hi leaf
  rw [hend] at hm
  have hh : GeometricDisclosure.MarkSupplied
      (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)) leaf j :=
    of_decide_eq_true hs
  obtain ht | ⟨hc,hj⟩ := hh
  · change j.val<_ at ht
    omega
  · exact ⟨hc,hj.symm⟩

theorem split_at_supply (hell : 0<ell) (q : Cursor L M ell S X A)
    (hq : Ready (state initial q)) (leaf : Leaf L) (j : Fin M) (N : ℕ)
    (hfinished : finished (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)=false)
    (hcurrent : TaskState.current (state initial
      (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q))=some leaf)
    (hindex : ((state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)).completed leaf).val=j.val) :
    ∃ k≤N,
      (∀ i<k,halt initial leaf j (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial i q)=false) ∧
      finished (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q)=false ∧
      TaskState.current (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q))=some leaf ∧
      ((state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q)).completed leaf).val=j.val ∧
      (ExternalHaltIteration.step (AugmentedNumericalCursorCounts.step P R (fun _ => false) o v initial)
        (halt initial leaf j))^[k] q=AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q ∧
      AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial (N-k)
        (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q)=
          AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q ∧
      ∀ m,k≤m →
        (ExternalHaltIteration.step (AugmentedNumericalCursorCounts.step P R (fun _ => false) o v initial)
          (halt initial leaf j))^[m] q=AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q := by
  have hs : AugmentedDisclosure.markStop leaf j
      (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q))=true := by
    apply decide_eq_true
    exact Or.inr ⟨hcurrent,hindex.symm⟩
  have hh : halt initial leaf j
      ((AugmentedNumericalCursorCounts.step P R (fun _ => false) o v initial)^[N] q)=true := by
    change halt initial leaf j (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial N q)=true
    simp only [halt,hs,Bool.or_true]
  obtain ⟨k,hk,hstop,hpre,he,hafter⟩ := ExternalHaltIteration.first_stop
    (AugmentedNumericalCursorCounts.step P R (fun _ => false) o v initial) (halt initial leaf j) q N hh
  have hf := unfinished_prefix P R o v initial q N k hk hfinished
  have hs' : AugmentedDisclosure.markStop leaf j
      (state initial (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q))=true := by
    change halt initial leaf j (AugmentedNumericalCursorCounts.run P R (fun _ => false) o v initial k q)=true at hstop
    simpa only [halt,hf,Bool.false_or] using hstop
  have hi := supplied_prefix_index P R o v initial hell q hq leaf j N k hk hindex hs'
  refine ⟨k,hk,hpre,hf,hi.1,hi.2,he,?_,hafter⟩
  simp only [AugmentedNumericalCursorCounts.run,← Function.iterate_add_apply,Nat.sub_add_cancel hk]

end GradientHessian.AugmentedNumericalSupplySplit
