import GradientHessian.PolicyEarlyIntegrability

/-! Exact task-indexed events for actual normal-early completions. A task
can complete early at most once; the total count is its finite event sum. -/

noncomputable section
namespace GradientHessian.ControllerEarlyEvents
open Classical FrontierState TaskState TaskSlots ComparisonController ComparisonControllerLedger
  VisibilityWindow VisibilityTaskWindow
open scoped BigOperators

variable {L M ell : ℕ} {X A : Type*}

abbrev Task (L M : ℕ) := Leaf L × Fin M

def earlyFor (R : Rules L M ell X A) (p : Pending X) (s : State L M ell) (q : Task L M) : ℕ :=
  if TaskState.current (serve R p s).beforeNormal=some q.1 ∧
      ((serve R p s).beforeNormal.completed q.1).val=q.2.val then early R p s else 0

theorem early_le_one (R : Rules L M ell X A) (p : Pending X) (s : State L M ell) : early R p s≤1 := by
  unfold early earlyCost
  cases p.kind <;> cases TaskState.current (serve R p s).beforeNormal <;> simp only
  all_goals first | omega | (split_ifs <;> omega)

theorem earlyFor_le_one (R : Rules L M ell X A) (p : Pending X) (s : State L M ell) (q : Task L M) :
    earlyFor R p s q≤1 := by
  unfold earlyFor
  split_ifs
  · exact early_le_one R p s
  · omega

theorem earlyFor_one_spec (R : Rules L M ell X A) (p : Pending X) (s : State L M ell) (q : Task L M)
    (he : earlyFor R p s q=1) :
    TaskState.current (serve R p s).beforeNormal=some q.1 ∧
      ((serve R p s).beforeNormal.completed q.1).val=q.2.val ∧ early R p s=1 := by
  unfold earlyFor at he
  split_ifs at he with h
  · exact ⟨h.1,h.2,he⟩

theorem sum_earlyFor (R : Rules L M ell X A) (p : Pending X) (s : State L M ell) :
    (∑ q : Task L M,earlyFor R p s q)=early R p s := by
  cases hc : TaskState.current (serve R p s).beforeNormal with
  | none => cases hk : p.kind <;> simp [earlyFor,hc,early,earlyCost,hk]
  | some leaf =>
    let j : Fin M := ⟨((serve R p s).beforeNormal.completed leaf).val,current_live _ hc⟩
    calc
      _ = earlyFor R p s (leaf,j) := by
        apply Finset.sum_eq_single (leaf,j)
        · intro q _ hne
          apply if_neg
          rintro ⟨hcur,hj⟩
          have hleaf : q.1=leaf := (Option.some.inj (hc.symm.trans hcur)).symm
          have htask : q.2=j := by
            apply Fin.ext
            change q.2.val=((serve R p s).beforeNormal.completed leaf).val
            rw [hleaf] at hj
            exact hj.symm
          exact hne (Prod.ext hleaf htask)
        · intro h
          exact (h (Finset.mem_univ _)).elim
      _ = _ := if_pos ⟨hc,rfl⟩

theorem earlyFor_completes (R : Rules L M ell X A) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (q : Task L M) (he : earlyFor R p s q=1) :
    q.2.val<((serve R p s).afterNormal.completed q.1).val := by
  obtain ⟨hc,hj,hcost⟩ := earlyFor_one_spec R p s q he
  have hb := repairRun_ready R p (8^L) hs
  cases hk : p.kind with
  | rich => simp [early,earlyCost,hk] at hcost
  | ordinary =>
    have hhit : R.hit (serve R p s).beforeNormal p.point=true := by
      unfold early earlyCost at hcost
      simp only [hk,hc] at hcost
      split_ifs at hcost with hh
      · exact hh.1
    change q.2.val<((normal R p (serve R p s).beforeNormal).completed q.1).val
    simp only [normal,hk]
    rw [ordinaryStep_eq _ _ hc (hb.2 q.1 (current_live _ hc)),if_pos (Or.inl hhit)]
    rw [completeLeaf_completed _ q.1 (by simpa only [advanceSlot_completed] using current_live _ hc),
      advanceSlot_completed,hj]
    omega

def finishedBit (s : State L M ell) (q : Task L M) : ℕ := if q.2.val<(s.completed q.1).val then 1 else 0

theorem finishedBit_le_one (s : State L M ell) (q : Task L M) : finishedBit s q≤1 := by
  unfold finishedBit
  split_ifs <;> omega

theorem finishedBit_mono (s u : State L M ell) (q : Task L M)
    (hm : (s.completed q.1).val≤(u.completed q.1).val) : finishedBit s q≤finishedBit u q := by
  unfold finishedBit
  split_ifs <;> omega

theorem earlyFor_credit (R : Rules L M ell X A) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (q : Task L M) :
    earlyFor R p s q+finishedBit s q≤finishedBit (serve R p s).afterNormal q := by
  by_cases hz : earlyFor R p s q=0
  · rw [hz,Nat.zero_add]
    exact finishedBit_mono s _ q (serve_completed_mono R p hs q.1)
  · have he : earlyFor R p s q=1 := by have hb := earlyFor_le_one R p s q; omega
    obtain ⟨_,hj,_⟩ := earlyFor_one_spec R p s q he
    have hpre := repairRun_completed_mono R p (8^L) s q.1
    change (s.completed q.1).val≤((serve R p s).beforeNormal.completed q.1).val at hpre
    rw [hj] at hpre
    simp only [he,finishedBit,if_neg (not_lt_of_ge hpre),
      if_pos (earlyFor_completes R p hs q he),Nat.add_zero,le_refl]

def count (R : Rules L M ell X A) (ps : List (Pending X)) (s : State L M ell) (q : Task L M) : ℕ :=
  tally R (fun p s => earlyFor R p s q) ps s

theorem count_credit (R : Rules L M ell X A) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0<ell) (q : Task L M) :
    count R ps s q+finishedBit s q≤finishedBit (VisibilityWindow.run R ps s) q := by
  induction ps generalizing s with
  | nil => simp [count,tally,VisibilityWindow.run]
  | cons p ps ih =>
    have ht := ih (serve_ready R p hs hell)
    have hp := earlyFor_credit R p hs q
    simp only [count,tally,VisibilityWindow.run] at *
    omega

theorem count_le_one (R : Rules L M ell X A) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0<ell) (q : Task L M) : count R ps s q≤1 := by
  have hc := count_credit R ps hs hell q
  have hb := finishedBit_le_one (VisibilityWindow.run R ps s) q
  omega

theorem count_sum (R : Rules L M ell X A) (ps : List (Pending X)) (s : State L M ell) :
    (∑ q : Task L M,count R ps s q)=tally R (early R) ps s := by
  induction ps generalizing s with
  | nil => simp [count,tally]
  | cons p ps ih =>
    change (∑ q : Task L M, (earlyFor R p s q + count R ps (serve R p s).afterNormal q)) =
      early R p s + tally R (early R) ps (serve R p s).afterNormal
    rw [Finset.sum_add_distrib,sum_earlyFor,ih]

theorem count_eq_event_bit (R : Rules L M ell X A) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0<ell) (q : Task L M) :
    count R ps s q=if 0<count R ps s q then 1 else 0 := by
  have hb := count_le_one R ps hs hell q
  split_ifs <;> omega

theorem early_eq_event_sum (R : Rules L M ell X A) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0<ell) :
    tally R (early R) ps s=∑ q : Task L M,if 0<count R ps s q then 1 else 0 := by
  rw [← count_sum]
  exact Finset.sum_congr rfl (fun q _ => count_eq_event_bit R ps hs hell q)

end GradientHessian.ControllerEarlyEvents
