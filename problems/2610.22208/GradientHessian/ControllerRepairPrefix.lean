import GradientHessian.ComparisonControllerReplay

/-! Repair-prefix states are genuine visits of the full atomic receipt.
These identities support ghost completion of the last pending query. -/

noncomputable section
namespace GradientHessian.ControllerRepairPrefix
open Classical FrontierState TaskState ComparisonController VisibilityWindow ComparisonControllerReplay

variable {L M ell : ℕ} {X A : Type*}

theorem repair_state_add (R : Rules L M ell X A) (p : Pending X) (n k : ℕ) (s : State L M ell) :
    (repairRun R p (n+k) s).1=(repairRun R p k (repairRun R p n s).1).1 := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add,repairRun]
  | succ n ih =>
    cases hc : choose R p s with
    | none =>
      cases k <;> simp [repairRun,hc]
    | some a => simpa only [Nat.succ_add,repairRun,hc] using ih (retireNode s (R.target a))

theorem repair_state_succ (R : Rules L M ell X A) (p : Pending X) (n : ℕ) (s : State L M ell) :
    (repairRun R p (n+1) s).1=
      match choose R p (repairRun R p n s).1 with
      | none => (repairRun R p n s).1
      | some a => retireNode (repairRun R p n s).1 (R.target a) := by
  rw [repair_state_add]
  cases hc : choose R p (repairRun R p n s).1 <;> simp [repairRun,hc]

theorem repair_state_terminal (R : Rules L M ell X A) (p : Pending X) (n cap : ℕ)
    (s : State L M ell) (hn : n≤cap) (hc : choose R p (repairRun R p n s).1=none) :
    (repairRun R p n s).1=(repairRun R p cap s).1 := by
  rw [show cap=n+(cap-n) by omega,repair_state_add]
  cases cap-n <;> simp [repairRun,hc]

theorem repair_prefix_mem_visits (R : Rules L M ell X A) (p : Pending X) (n cap : ℕ)
    (s : State L M ell) (hn : n≤cap) : (repairRun R p n s).1 ∈ visits R p cap s := by
  induction cap generalizing n s with
  | zero =>
    have he : n=0 := by omega
    subst n
    simp [visits,repairRun]
  | succ cap ih =>
    cases hc : choose R p s with
    | none => cases n <;> simp [visits,repairRun,hc]
    | some a =>
      cases n with
      | zero => simp [visits,repairRun,hc]
      | succ n =>
        have hi := ih n (retireNode s (R.target a)) (by omega)
        simpa only [visits,repairRun,hc,List.map_cons,List.cons_append,List.mem_cons,
          List.mem_append] using Or.inr hi

theorem repair_prefix_lt_cap_of_choice (R : Rules L M ell X A) (p : Pending X) (n : ℕ)
    (s : State L M ell) (hn : n≤8^L) (a : A)
    (hc : choose R p (repairRun R p n s).1=some a) : n<8^L := by
  by_contra hh
  have he : n=8^L := by omega
  subst n
  have ht := repairRun_terminal R p (8^L) s ((Finset.card_le_univ _).trans_eq (leaf_card L))
  rw [hc] at ht
  contradiction

theorem controller_run_append (R : Rules L M ell X A) (ps qs : List (Pending X)) (s : State L M ell) :
    VisibilityWindow.run R (ps++qs) s=VisibilityWindow.run R qs (VisibilityWindow.run R ps s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => exact ih (serve R p s).afterNormal

theorem seenPoints_append (R : Rules L M ell X A) (v : Node L)
    (ps qs : List (Pending X)) (s : State L M ell) :
    seenPoints R v (ps++qs) s=seenPoints R v ps s ++ seenPoints R v qs (VisibilityWindow.run R ps s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.cons_append,seenPoints,VisibilityWindow.run]
    split_ifs <;> simp [ih]

theorem pending_visible_mem_seenPoints (R : Rules L M ell X A) (v : Node L)
    (pre suffix : List (Pending X)) (p : Pending X) (s : State L M ell) (n : ℕ)
    (hn : n≤8^L)
    (hv : Visible (TaskState.retired (repairRun R p n (VisibilityWindow.run R pre s)).1) v) :
    p.point ∈ seenPoints R v (pre++p::suffix) s := by
  rw [seenPoints_append]
  apply List.mem_append_right
  have hs : Seen R p (VisibilityWindow.run R pre s) v :=
    ⟨_,repair_prefix_mem_visits R p n (8^L) _ hn,hv⟩
  simp only [seenPoints,if_pos hs,List.mem_cons]
  exact Or.inl trivial

end GradientHessian.ControllerRepairPrefix
