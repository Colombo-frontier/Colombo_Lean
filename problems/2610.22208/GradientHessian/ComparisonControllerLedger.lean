import GradientHessian.VisibilityTaskWindow

/-!
# The actual controller's deterministic task ledger

Repair cost is the sum of newly retired tasks in the chronological repair
trace. Early completions are strictly before timeout. These counts are
computed from transitions, rather than supplied as a ledger hypothesis.
-/

noncomputable section
namespace GradientHessian.ComparisonControllerLedger

open Classical FrontierState TaskState TaskSlots ComparisonController VisibilityWindow
open scoped BigOperators

variable {L M ell : ℕ} {X Action : Type*}

def repairCharge (R : Rules L M ell X Action) (p : Pending X) (n : ℕ) (s : State L M ell) : ℕ :=
  ((repairRun R p n s).2.map fun frame => charge frame.1 (subtree (R.target frame.2))).sum

theorem repairCharge_exact (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) :
    completedTotal (repairRun R p n s).1=completedTotal s+repairCharge R p n s := by
  induction n generalizing s with
  | zero => simp [repairRun,repairCharge]
  | succ n ih =>
    cases ha : choose R p s with
    | none => simp [repairRun,repairCharge,ha]
    | some a =>
      have hi := ih (retireNode s (R.target a))
      rw [retireNode_charge] at hi
      simpa [repairRun,repairCharge,ha,Nat.add_assoc] using hi

def ordinaryCost (p : Pending X) (s : State L M ell) : ℕ :=
  match p.kind,TaskState.current s with | .ordinary,some _ => 1 | _,_ => 0

def richCost (p : Pending X) (s : State L M ell) : ℕ :=
  match p.kind,TaskState.current s with | .rich,some _ => 1 | _,_ => 0

def earlyCost (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : ℕ :=
  match p.kind,TaskState.current s with
  | .ordinary,some leaf => if R.hit s p.point=true ∧ (s.slots leaf).val+1<ell then 1 else 0
  | _,_ => 0

def timeoutCost (p : Pending X) (s : State L M ell) : ℕ :=
  match p.kind,TaskState.current s with
  | .ordinary,some leaf => if (s.slots leaf).val+1=ell then 1 else 0
  | _,_ => 0

def richCharge (p : Pending X) (s : State L M ell) : ℕ :=
  match p.kind,TaskState.current s with | .rich,some leaf => remaining s leaf | _,_ => 0

theorem normal_completed_exact (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) :
    completedTotal (normal R p s)=completedTotal s+earlyCost R p s+timeoutCost p s+richCharge p s := by
  cases hc : TaskState.current s with
  | none => cases hk : p.kind <;> simp [normal,ordinaryStep,richComplete,earlyCost,timeoutCost,richCharge,hk,hc]
  | some leaf =>
    cases hk : p.kind with
    | rich => simpa [normal,earlyCost,timeoutCost,richCharge,hk,hc] using richComplete_charge s hc
    | ordinary =>
      have hslot := hs.2 leaf (current_live s hc)
      simp only [normal,earlyCost,timeoutCost,richCharge,hk,hc,Nat.add_zero]
      rw [ordinaryStep_completedTotal _ s hc hslot]
      by_cases ht : (s.slots leaf).val+1=ell
      · simp [ht]
      · have hlt : (s.slots leaf).val+1<ell := by omega
        by_cases hh : R.hit s p.point=true <;> simp [ht,hlt,hh]

theorem richCharge_le (p : Pending X) (s : State L M ell) : richCharge p s ≤ richCost p s*M := by
  cases hc : TaskState.current s <;> cases hk : p.kind <;>
    simp [richCharge,richCost,remaining,hk,hc]

def slotSum (s : State L M ell) : ℕ := ∑ leaf,(s.slots leaf).val

theorem retireSet_slots_le (s : State L M ell) (S : Finset (Leaf L)) (leaf : Leaf L) :
    ((retireSet s S).slots leaf).val ≤ (s.slots leaf).val := by
  by_cases hl : leaf ∈ S
  · simp only [retireSet,if_pos hl,Fin.val_zero]
    exact Nat.zero_le _
  · simp only [retireSet,if_neg hl,le_refl]

theorem repairRun_slots_le (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) (leaf : Leaf L) :
    ((repairRun R p n s).1.slots leaf).val ≤ (s.slots leaf).val := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    cases ha : choose R p s with
    | none => simp [repairRun,ha]
    | some a =>
      exact (show ((repairRun R p (n+1) s).1.slots leaf).val ≤
          ((retireNode s (R.target a)).slots leaf).val by
        simpa [repairRun,ha] using ih (retireNode s (R.target a))).trans
        (retireSet_slots_le s (subtree (R.target a)) leaf)

theorem repairRun_slotSum_le (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) : slotSum (repairRun R p n s).1 ≤ slotSum s :=
  Finset.sum_le_sum (fun leaf _ => repairRun_slots_le R p n s leaf)

theorem sum_balance {I : Type*} [Fintype I] (f g : I → ℕ) (i : I)
    (h : ∀ j,j ≠ i → f j=g j) : (∑ j,f j)+g i=(∑ j,g j)+f i := by
  have he : (∑ j,(f j+(if j=i then g i else 0)))=(∑ j,(g j+(if j=i then f i else 0))) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=i
    · subst j; simp [Nat.add_comm]
    · simp [hj,h j hj]
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] using he

theorem normal_timeout_credit (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) :
    timeoutCost p s*ell+slotSum (normal R p s) ≤ slotSum s+ordinaryCost p s := by
  cases hc : TaskState.current s with
  | none => cases hk : p.kind <;> simp [normal,ordinaryStep,richComplete,timeoutCost,ordinaryCost,hk,hc]
  | some leaf =>
    cases hk : p.kind with
    | rich =>
      simp only [normal,hk,richComplete,hc,timeoutCost,ordinaryCost,Nat.zero_mul,Nat.zero_add,Nat.add_zero]
      exact Finset.sum_le_sum (fun other _ => retireSet_slots_le s {leaf} other)
    | ordinary =>
      have hslot := hs.2 leaf (current_live s hc)
      have hbalance := sum_balance (fun other => ((ordinaryStep (R.hit s p.point) s).slots other).val)
        (fun other => (s.slots other).val) leaf
        (fun other ho => congrArg Fin.val (ordinaryStep_other _ s hc other ho).2)
      change slotSum (ordinaryStep (R.hit s p.point) s)+(s.slots leaf).val=
        slotSum s+((ordinaryStep (R.hit s p.point) s).slots leaf).val at hbalance
      rw [ordinaryStep_slots _ s hc hslot] at hbalance
      simp only [normal,hk,timeoutCost,ordinaryCost,hc]
      by_cases ht : (s.slots leaf).val+1=ell
      · simp only [if_pos ht,one_mul]
        simp only [ht,or_true,if_true,Nat.add_zero] at hbalance
        omega
      · simp only [if_neg ht,Nat.zero_mul,Nat.zero_add]
        split_ifs at hbalance <;> omega

/-- Sum a genuine per-reply transition count along the selected history. -/
def tally (R : Rules L M ell X Action) (cost : Pending X → State L M ell → ℕ) :
    List (Pending X) → State L M ell → ℕ
  | [],_ => 0
  | p::ps,s => cost p s+tally R cost ps (serve R p s).afterNormal

def ordinary (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : ℕ :=
  ordinaryCost p (serve R p s).beforeNormal
def rich (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : ℕ :=
  richCost p (serve R p s).beforeNormal
def early (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : ℕ :=
  earlyCost R p (serve R p s).beforeNormal
def timeout (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : ℕ :=
  timeoutCost p (serve R p s).beforeNormal
def repairs (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : ℕ :=
  repairCharge R p (8^L) s

theorem serve_completed_ledger (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) :
    completedTotal (serve R p s).afterNormal ≤ completedTotal s+
      rich R p s*M+early R p s+timeout R p s+repairs R p s := by
  have he := normal_completed_exact R p (repairRun_ready R p (8^L) hs)
  rw [repairCharge_exact] at he
  have hb := richCharge_le p (repairRun R p (8^L) s).1
  change completedTotal (normal R p (repairRun R p (8^L) s).1) ≤ _
  simp only [rich,early,timeout,repairs,serve]
  omega

theorem serve_timeout_credit (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) :
    timeout R p s*ell+slotSum (serve R p s).afterNormal ≤ slotSum s+ordinary R p s := by
  have hn := normal_timeout_credit R p (repairRun_ready R p (8^L) hs)
  have hr := repairRun_slotSum_le R p (8^L) s
  change timeoutCost p (repairRun R p (8^L) s).1*ell+
      slotSum (normal R p (repairRun R p (8^L) s).1) ≤
      slotSum s+ordinaryCost p (repairRun R p (8^L) s).1
  omega

theorem run_completed_ledger (R : Rules L M ell X Action) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    completedTotal (run R ps s) ≤ completedTotal s+tally R (rich R) ps s*M+
      tally R (early R) ps s+tally R (timeout R) ps s+tally R (repairs R) ps s := by
  induction ps generalizing s with
  | nil => simp [run,tally]
  | cons p ps ih =>
    have hi := ih (serve_ready R p hs hell)
    have hp := serve_completed_ledger R p hs
    simp only [run,tally,Nat.add_mul]
    omega

theorem run_timeout_credit (R : Rules L M ell X Action) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    tally R (timeout R) ps s*ell+slotSum (run R ps s) ≤ slotSum s+tally R (ordinary R) ps s := by
  induction ps generalizing s with
  | nil => simp [run,tally]
  | cons p ps ih =>
    have hi := ih (serve_ready R p hs hell)
    have hp := serve_timeout_credit R p hs
    simp only [run,tally,Nat.add_mul]
    omega

theorem all_retired_completed {s : State L M ell} (hs : TaskState.retired s=Finset.univ) :
    completedTotal s=8^L*M := by
  have he leaf : (s.completed leaf).val=M := (mem_retired _ _).mp (by rw [hs]; exact Finset.mem_univ _)
  simp [completedTotal,he,leaf_card]

/-- The manuscript's pathwise task ledger, for the actual controller counts.
The selected list may include the virtual ordinary output as its last entry. -/
theorem all_retired_task_ledger (R : Rules L M ell X Action) (ps : List (Pending X))
    (hell : 0 < ell) (hretired : TaskState.retired (run R ps initial)=Finset.univ) :
    8^L*M ≤ tally R (rich R) ps initial*M+tally R (ordinary R) ps initial/ell+
      tally R (early R) ps initial+tally R (repairs R) ps initial := by
  have hc := run_completed_ledger R ps (initial_ready hell) hell
  have ht := run_timeout_credit R ps (initial_ready hell) hell
  have he := all_retired_completed hretired
  have hdiv : tally R (timeout R) ps initial ≤ tally R (ordinary R) ps initial/ell := by
    apply (Nat.le_div_iff_mul_le hell).mpr
    simpa only [slotSum,initial,Fin.val_zero,Finset.sum_const_zero,Nat.zero_add] using
      (le_trans (Nat.le_add_right _ _) ht)
  have hinit : completedTotal (initial : State L M ell)=0 := by simp [completedTotal,initial]
  rw [he,hinit] at hc
  omega

end GradientHessian.ComparisonControllerLedger
