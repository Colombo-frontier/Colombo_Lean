import GradientHessian.ExternalHaltIteration
import GradientHessian.ControllerPostWindow

/-! Splitting an actual chronological driver at the first mark supply.
The saved state and both pending reply snapshots are retained literally. -/

noncomputable section
namespace GradientHessian.NumericalSupplySplit
open Classical FrontierState TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerDriverMonotonicity ControllerDriverResource

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)

theorem run_iterate (N : ℕ) (q : Config L M ell S X A) :
    run P R (fun _ => false) o v N q=(step P R (fun _ => false) o v)^[N] q := by
  induction N generalizing q with
  | zero => rfl
  | succ N ih => rw [run,Function.iterate_succ_apply,ih]

theorem unfinished_prefix (q : Config L M ell S X A) (N i : ℕ) (hi : i≤N)
    (hN : NumericalDriverInstructions.finished (run P R (fun _ => false) o v N q)=false) :
    NumericalDriverInstructions.finished (run P R (fun _ => false) o v i q)=false := by
  cases he : run P R (fun _ => false) o v i q with
  | ready => rfl
  | pending => rfl
  | finished a s =>
      have hn : run P R (fun _ => false) o v N q=.finished a s := by
        rw [← Nat.add_sub_of_le hi,run_add,he,run_finished]
      rw [hn] at hN
      cases hN

theorem completed_prefix (hell : 0<ell) (q : Config L M ell S X A) (hq : Ready (stateOf q))
    (N i : ℕ) (hi : i≤N) (leaf : Leaf L) :
    ((stateOf (run P R (fun _ => false) o v i q)).completed leaf).val≤
      ((stateOf (run P R (fun _ => false) o v N q)).completed leaf).val := by
  have hh := run_completed_mono P R (fun _ => false) o v hell
    (run P R (fun _ => false) o v i q) (run_good P R (fun _ => false) o v hell q hq i) (N-i) leaf
  rw [← run_add,Nat.add_sub_of_le hi] at hh
  exact hh

theorem supplied_prefix_index (hell : 0<ell) (q : Config L M ell S X A) (hq : Ready (stateOf q))
    (leaf : Leaf L) (j : Fin M) (N i : ℕ) (hi : i≤N)
    (hend : ((stateOf (run P R (fun _ => false) o v N q)).completed leaf).val=j.val)
    (hs : markSupplied leaf j (stateOf (run P R (fun _ => false) o v i q))=true) :
    TaskState.current (stateOf (run P R (fun _ => false) o v i q))=some leaf ∧
      ((stateOf (run P R (fun _ => false) o v i q)).completed leaf).val=j.val := by
  have hm := completed_prefix P R o v hell q hq N i hi leaf
  rw [hend] at hm
  obtain hr | ⟨hc,hj⟩ := of_decide_eq_true hs
  · have he := (mem_retired _ _).mp hr
    have hl := j.isLt
    omega
  · exact ⟨hc,by omega⟩

def halt (leaf : Leaf L) (j : Fin M) (q : Config L M ell S X A) : Bool :=
  NumericalDriverInstructions.finished q || markSupplied leaf j (stateOf q)

theorem split_at_supply (hell : 0<ell) (q : Config L M ell S X A) (hq : Ready (stateOf q))
    (leaf : Leaf L) (j : Fin M) (N : ℕ)
    (hfinished : NumericalDriverInstructions.finished (run P R (fun _ => false) o v N q)=false)
    (hcurrent : TaskState.current (stateOf (run P R (fun _ => false) o v N q))=some leaf)
    (hindex : ((stateOf (run P R (fun _ => false) o v N q)).completed leaf).val=j.val) :
    ∃ k≤N,
      (∀ i<k,halt leaf j (run P R (fun _ => false) o v i q)=false) ∧
      NumericalDriverInstructions.finished (run P R (fun _ => false) o v k q)=false ∧
      TaskState.current (stateOf (run P R (fun _ => false) o v k q))=some leaf ∧
      ((stateOf (run P R (fun _ => false) o v k q)).completed leaf).val=j.val ∧
      (ExternalHaltIteration.step (step P R (fun _ => false) o v) (halt leaf j))^[k] q=
        run P R (fun _ => false) o v k q ∧
      run P R (fun _ => false) o v (N-k) (run P R (fun _ => false) o v k q)=
        run P R (fun _ => false) o v N q := by
  have hs : markSupplied leaf j (stateOf (run P R (fun _ => false) o v N q))=true := by
    apply decide_eq_true
    exact Or.inr ⟨hcurrent,by omega⟩
  have hh : halt leaf j ((step P R (fun _ => false) o v)^[N] q)=true := by
    rw [← run_iterate]
    simp [halt,hs]
  obtain ⟨k,hk,hstop,hpre,he,_⟩ := ExternalHaltIteration.first_stop
    (step P R (fun _ => false) o v) (halt leaf j) q N hh
  have hf := unfinished_prefix P R o v q N k hk hfinished
  have hs' : markSupplied leaf j (stateOf (run P R (fun _ => false) o v k q))=true := by
    rw [← run_iterate] at hstop
    simpa only [halt,hf,Bool.false_or] using hstop
  have hi := supplied_prefix_index P R o v hell q hq leaf j N k hk hindex hs'
  refine ⟨k,hk,?_,hf,hi.1,hi.2,?_,?_⟩
  · intro i hi
    rw [run_iterate]
    exact hpre i hi
  · simpa only [run_iterate] using he
  · rw [← run_add,Nat.add_sub_of_le hk]

end GradientHessian.NumericalSupplySplit
