import GradientHessian.ComparisonController

/-! Exact correspondence between finite internal repair phases and the
atomic receipt. Internal steps keep the pending point fixed; repair steps
never increment an ordinary slot, and delivery is absorbing. -/

noncomputable section
namespace GradientHessian.ComparisonControllerPhases

open Classical FrontierState TaskState TaskSlots ComparisonController

variable {L M ell : ℕ} {X Action : Type*}

def ticks (R : Rules L M ell X Action) :
    ℕ → Phase L M ell X Action → Phase L M ell X Action
  | 0,q => q
  | n+1,q => ticks R n (tick R q)

theorem ticks_succ_end (R : Rules L M ell X Action) (n : ℕ) (q : Phase L M ell X Action) :
    ticks R (n+1) q=tick R (ticks R n q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => exact ih (tick R q)

@[simp] theorem ticks_point (R : Rules L M ell X Action) (n : ℕ) (q : Phase L M ell X Action) :
    point (ticks R n q)=point q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp only [ticks,ih,tick_point]

@[simp] theorem ticks_delivered (R : Rules L M ell X Action) (n : ℕ)
    (p : Pending X) (before after : State L M ell) :
    ticks R n (.delivered p before after)=.delivered p before after := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem ticks_frozen (R : Rules L M ell X Action) (n : ℕ)
    (p : Pending X) (s : State L M ell) : ticks R n (.frozen p s)=.frozen p s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem repair_tick_slots_le (R : Rules L M ell X Action) (p : Pending X)
    (s : State L M ell) {a : Action} (ha : choose R p s=some a) (leaf : Leaf L) :
    tick R (.repairing p s)=.repairing p (retireNode s (R.target a)) ∧
      ((retireNode s (R.target a)).slots leaf).val ≤ (s.slots leaf).val := by
  constructor
  · simp [tick,ha]
  · by_cases hl : leaf ∈ subtree (R.target a)
    · simp only [retireNode,retireSet,if_pos hl,Fin.val_zero]
      exact Nat.zero_le _
    · simp only [retireNode,retireSet,if_neg hl,le_refl]

theorem repairRun_realized (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) (hn : (unretired (TaskState.retired s)).card ≤ n) :
    ticks R ((repairRun R p n s).2.length+1) (.repairing p s)=
      .normal p (repairRun R p n s).1 := by
  induction n generalizing s with
  | zero =>
    have hc := repairRun_terminal R p 0 s hn
    change choose R p s=none at hc
    simp [repairRun,ticks,tick,hc]
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [repairRun,ticks,tick,hc]
    | some a =>
      have hp := retirement_progress (TaskState.retired s) (R.target a) (choose_spec R p s hc).2.2
      have hb : (unretired (TaskState.retired (retireNode s (R.target a)))).card ≤ n := by
        rw [retireNode_retired]
        omega
      simpa [repairRun,List.length_cons,ticks,tick,hc] using ih (retireNode s (R.target a)) hb

/-- Exactly repairs.length repair steps, one stable-phase transition, and
one normal operation produce the snapshots stored by serve. -/
theorem serve_realized (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    ticks R ((serve R p s).repairs.length+2) (.repairing p s)=
      .delivered p (serve R p s).beforeNormal (serve R p s).afterNormal := by
  have hr := repairRun_realized R p (8^L) s
    ((Finset.card_le_univ _).trans_eq (leaf_card L))
  change ticks R ((repairRun R p (8^L) s).2.length+1+1) (.repairing p s)=_
  rw [ticks_succ_end,hr]
  rfl

theorem serve_internal_steps_le (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    (serve R p s).repairs.length+2 ≤ 8^L+2 := by
  have := serve_repairs_length R p s
  omega

end GradientHessian.ComparisonControllerPhases
