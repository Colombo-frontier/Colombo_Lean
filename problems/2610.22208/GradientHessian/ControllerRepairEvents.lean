import GradientHessian.ComparisonControllerLedger

/-! Repair actions in an actual chronological execution occur at most once.
This turns trace charges into a sum over repair events, before any probability
bound is applied. -/

noncomputable section
namespace GradientHessian.ControllerRepairEvents
open Classical FrontierState TaskState TaskSlots ComparisonController
  VisibilityWindow VisibilityTaskWindow ComparisonControllerLedger

variable {L M ell : ℕ} {X Action : Type*}

def pointActions (R : Rules L M ell X Action) (p : Pending X) (n : ℕ) (s : State L M ell) : List Action :=
  (repairRun R p n s).2.map Prod.snd

theorem retireNode_target (s : State L M ell) (v : Node L) :
    subtree v ⊆ TaskState.retired (retireNode s v) := by
  rw [retireNode_retired]
  exact Finset.subset_union_right

theorem point_mem_retired (R : Rules L M ell X Action) (p : Pending X) (n : ℕ)
    (s : State L M ell) {a : Action} (ha : a ∈ pointActions R p n s) :
    subtree (R.target a) ⊆ TaskState.retired (repairRun R p n s).1 := by
  induction n generalizing s with
  | zero => simp [pointActions,repairRun] at ha
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [pointActions,repairRun,hc] at ha
    | some b =>
      have hm : a=b ∨ a ∈ pointActions R p n (retireNode s (R.target b)) := by
        simpa [pointActions,repairRun,hc] using ha
      rcases hm with rfl | hm
      · exact (retireNode_target s (R.target a)).trans
          (by simpa [repairRun,hc] using repairRun_retired_mono R p n (retireNode s (R.target a)))
      · simpa [repairRun,hc] using ih (retireNode s (R.target b)) hm

theorem point_mem_live (R : Rules L M ell X Action) (p : Pending X) (n : ℕ)
    (s : State L M ell) {a : Action} (ha : a ∈ pointActions R p n s) :
    ¬subtree (R.target a) ⊆ TaskState.retired s := by
  induction n generalizing s with
  | zero => simp [pointActions,repairRun] at ha
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [pointActions,repairRun,hc] at ha
    | some b =>
      have hm : a=b ∨ a ∈ pointActions R p n (retireNode s (R.target b)) := by
        simpa [pointActions,repairRun,hc] using ha
      rcases hm with rfl | hm
      · intro hsub
        obtain ⟨leaf,hl⟩ := (choose_spec R p s hc).2.2
        exact (Finset.mem_sdiff.mp hl).2 (hsub (Finset.mem_sdiff.mp hl).1)
      · intro hsub
        apply ih (retireNode s (R.target b)) hm
        exact hsub.trans (by rw [retireNode_retired]; exact Finset.subset_union_left)

theorem pointActions_nodup (R : Rules L M ell X Action) (p : Pending X) (n : ℕ) (s : State L M ell) :
    (pointActions R p n s).Nodup := by
  induction n generalizing s with
  | zero => simp [pointActions,repairRun]
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [pointActions,repairRun,hc]
    | some a =>
      have he : pointActions R p (n+1) s = a::pointActions R p n (retireNode s (R.target a)) := by
        simp [pointActions,repairRun,hc]
      rw [he,List.nodup_cons]
      refine ⟨?_,ih _⟩
      intro ha
      exact point_mem_live R p n _ ha (retireNode_target s (R.target a))

def actionCost (R : Rules L M ell X Action) (a : Action) : ℕ := (subtree (R.target a)).card*M

theorem point_charge_le (R : Rules L M ell X Action) (p : Pending X) (n : ℕ) (s : State L M ell) :
    repairCharge R p n s ≤ ((pointActions R p n s).map (actionCost R)).sum := by
  induction n generalizing s with
  | zero => simp [repairCharge,pointActions,repairRun]
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [repairCharge,pointActions,repairRun,hc]
    | some a =>
      have hi := ih (retireNode s (R.target a))
      have hcost := TaskState.charge_le s (subtree (R.target a))
      simpa [repairCharge,pointActions,repairRun,hc,actionCost,List.map_map] using Nat.add_le_add hcost hi

theorem normal_retired_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) : TaskState.retired s ⊆ TaskState.retired (normal R p s) := by
  intro leaf hl
  apply (mem_retired _ _).mpr
  have hm := normal_completed_mono R p hs leaf
  have he := (mem_retired _ _).mp hl
  have hb := ((normal R p s).completed leaf).isLt
  omega

def actions (R : Rules L M ell X Action) : List (Pending X) → State L M ell → List Action
  | [],_ => []
  | p::ps,s => pointActions R p (8^L) s ++ actions R ps (serve R p s).afterNormal

theorem actions_mem_live (R : Rules L M ell X Action) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0<ell) {a : Action} (ha : a ∈ actions R ps s) :
    ¬subtree (R.target a) ⊆ TaskState.retired s := by
  induction ps generalizing s with
  | nil => simp [actions] at ha
  | cons p ps ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact point_mem_live R p _ s ha
    · intro hsub
      exact ih (serve_ready R p hs hell) ha (hsub.trans (serve_retired_mono R p hs))

theorem actions_nodup (R : Rules L M ell X Action) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0<ell) : (actions R ps s).Nodup := by
  induction ps generalizing s with
  | nil => simp [actions]
  | cons p ps ih =>
    rw [actions,List.nodup_append]
    refine ⟨pointActions_nodup R p _ s, ih (serve_ready R p hs hell), ?_⟩
    intro a ha hb
    apply actions_mem_live R ps (serve_ready R p hs hell) hell hb
    exact (point_mem_retired R p _ s ha).trans
      (normal_retired_mono R p (repairRun_ready R p _ hs))

theorem total_charge_le (R : Rules L M ell X Action) (ps : List (Pending X)) (s : State L M ell) :
    tally R (repairs R) ps s ≤ ((actions R ps s).map (actionCost R)).sum := by
  induction ps generalizing s with
  | nil => simp [tally,actions]
  | cons p ps ih =>
    have h1 := point_charge_le R p (8^L) s
    have h2 := ih (serve R p s).afterNormal
    simpa [tally,repairs,actions,List.map_append,List.sum_append] using Nat.add_le_add h1 h2

/-- Each public repair label contributes its cost at most once, across all
selected points and all intervening repairs. -/
theorem total_charge_le_sum [Fintype Action] (R : Rules L M ell X Action)
    (ps : List (Pending X)) {s : State L M ell} (hs : Ready s) (hell : 0<ell) :
    tally R (repairs R) ps s ≤
      ∑ a : Action, if a ∈ actions R ps s then actionCost R a else 0 := by
  classical
  have he : ((actions R ps s).map (actionCost R)).sum =
      ∑ a ∈ (actions R ps s).toFinset, actionCost R a :=
    (List.sum_toFinset _ (actions_nodup R ps hs hell)).symm
  refine (total_charge_le R ps s).trans_eq (he.trans ?_)
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp

theorem total_charge_le_public_sum [Fintype Action] (R : Rules L M ell X Action)
    (ps : List (Pending X)) {s : State L M ell} (hs : Ready s) (hell : 0<ell)
    (cost : Action → ℕ) (hcost : ∀ a, actionCost R a ≤ cost a) :
    tally R (repairs R) ps s ≤
      ∑ a : Action, if a ∈ actions R ps s then cost a else 0 := by
  refine (total_charge_le_sum R ps hs hell).trans (Finset.sum_le_sum ?_)
  intro a _
  split_ifs
  · exact hcost a
  · exact le_rfl

end GradientHessian.ControllerRepairEvents
