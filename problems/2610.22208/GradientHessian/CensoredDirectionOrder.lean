import GradientHessian.CensoredDirectionView
import GradientHessian.ControllerCensorPlan

/-! Actual retirement forces precisely the hidden branches and flags used
by direction erasure. A live leaf in the target subtree supplies the witness. -/

noncomputable section
namespace GradientHessian.CensoredDirection
open Classical FrontierState TaskState ControllerCensor GeometricDisclosure

theorem coordinate_le_of_prefix {L : ℕ} (a b : Leaf L) (k : Fin L) (hab : a≤b)
    (hp : ∀ j,j<k → a j=b j) : a k≤b k := by
  by_contra h
  have hba : b<a := ⟨k,fun j hj => (hp j hj).symm,lt_of_not_ge h⟩
  exact (not_lt_of_ge hab) hba

theorem hiddenAt_plan_of_witness {T m ell : ℕ}
    (before after : State (T+1) (m+1) ell) (cur witness : Leaf (T+1))
    (hc : TaskState.current before=some cur) (hle : cur≤witness)
    (h : ℕ) (endpoint : CensoredHierarchy.Plan m h → Prop) :
    ∀ (depth : ℕ) (ht : h+depth≤T) (w : HierarchyAddresses.Word depth),
    (∀ k : Fin (T-(h+depth)),cur ⟨k.val,by have := k.isLt; omega⟩=witness ⟨k.val,by have := k.isLt; omega⟩) →
    (∀ k : Fin depth,witness ⟨T-(h+depth)+k.val,by have := k.isLt; omega⟩=w k) →
    ((∀ k : Fin (T-h),cur ⟨k.val,by have := k.isLt; omega⟩=witness ⟨k.val,by have := k.isLt; omega⟩) →
      endpoint (planAt before after cur hc h)) →
    HiddenAt h endpoint depth w (planAt before after cur hc (h+depth)) := by
  intro depth
  induction depth with
  | zero => intro ht w hp hw hend; exact hend hp
  | succ depth ih =>
    intro ht w hp hw hend
    let pos : Fin (T+1) := ⟨T-(h+(depth+1)),by omega⟩
    have hp' : ∀ k,k<pos → cur k=witness k := by
      intro k hk
      exact hp ⟨k.val,hk⟩
    have hh := coordinate_le_of_prefix cur witness pos hle hp'
    have hw0 : witness pos=w 0 := by simpa only [pos,Nat.add_zero] using hw 0
    have hcur : currentChild cur (h+(depth+1))=cur pos := rfl
    rw [hw0] at hh
    rcases lt_or_eq_of_le hh with hl | he
    · exact Or.inl hl
    · apply Or.inr
      refine ⟨he,?_⟩
      apply ih (by omega) (Fin.tail w)
      · intro k
        by_cases hk : k.val<pos.val
        · exact hp' ⟨k.val,by have := k.isLt; omega⟩ hk
        · have hk' : k.val=pos.val := by have := k.isLt; dsimp [pos] at hk ⊢; omega
          have hc' : (⟨k.val,by have := k.isLt; omega⟩ : Fin (T+1))=pos := Fin.ext hk'
          rw [hc']
          exact he.trans hw0.symm
      · intro k
        have ha := hw k.succ
        convert ha using 1
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      · exact hend

theorem hiddenBlock_of_live_witness {h depth m ell : ℕ}
    (before after : State (h+depth+1) (m+1) ell) (cur witness : Leaf (h+depth+1))
    (hc : TaskState.current before=some cur)
    (hmono : TaskState.retired before⊆TaskState.retired after)
    (hn : witness∉TaskState.retired after) (w : HierarchyAddresses.Word depth) (i : Fin 8)
    (hw : ∀ k : Fin depth,witness ⟨k.val,by have := k.isLt; omega⟩=w k)
    (hi : witness ⟨depth,by omega⟩=i) :
    HiddenAt h (HiddenBlock i) depth w (planAt before after cur hc (h+depth)) := by
  have hle : cur≤witness := ((FrontierState.current_eq_some_iff _ _).mp hc).2 witness (fun he => hn (hmono he))
  apply hiddenAt_plan_of_witness before after cur witness hc hle h (HiddenBlock i) depth le_rfl w
  · intro k
    exact Fin.elim0 (Fin.cast (by omega) k)
  · intro k
    simpa only [Nat.sub_self,Nat.zero_add] using hw k
  · intro hp
    have hprefix : ∀ k : Fin (h+depth-h),witness (k.castLE (by omega))=(nodeAt cur h).2 k := by
      intro k
      exact (hp k).symm
    have hpos : witness ⟨h+depth-h,by omega⟩=i := by
      simpa only [Nat.add_sub_cancel_left] using hi
    have hmem : witness∈subtree (childAt cur h i) := by
      apply (mem_subtree _ _).mpr
      apply (inSubtree_child_iff _ _ _ _).mpr
      exact ⟨hprefix,hpos⟩
    have hcurr : currentChild cur h ≤ i := by
      rw [← hpos]
      apply coordinate_le_of_prefix cur witness _ hle
      intro k hk
      exact hp ⟨k.val,hk⟩
    have hknown : known after cur h i≠true := by
      intro he
      exact hn ((of_decide_eq_true he) hmem)
    cases h with
    | zero => exact fun he => he.elim (fun hl => (not_lt_of_ge hcurr) hl) hknown
    | succ h => exact fun he => he.elim (fun hl => (not_lt_of_ge hcurr) hl) hknown

def addressedNode (h depth : ℕ) (w : HierarchyAddresses.Word depth) : Node (h+depth+1) :=
  ⟨⟨depth,by omega⟩,w⟩

theorem hiddenBlock_controller {h depth m ell : ℕ}
    (before after : State (h+depth+1) (m+1) ell) (cur : Leaf (h+depth+1))
    (hc : TaskState.current before=some cur)
    (hmono : TaskState.retired before⊆TaskState.retired after)
    (w : HierarchyAddresses.Word depth) (i : Fin 8)
    (hd : ¬NodeDisclosed after (child (addressedNode h depth w) (by simp [addressedNode]; omega) i)) :
    HiddenAt h (HiddenBlock i) depth w (planAt before after cur hc (h+depth)) := by
  obtain ⟨witness,hm,hn⟩ := Finset.not_subset.mp hd
  have hc' := (inSubtree_child_iff _ _ _ _).mp ((mem_subtree _ _).mp hm)
  exact hiddenBlock_of_live_witness before after cur witness hc hmono hn w i hc'.1 hc'.2

theorem hiddenInner_controller {depth m ell : ℕ}
    (before after : State (0+depth+1) (m+1) ell) (cur target : Leaf (0+depth+1))
    (hc : TaskState.current before=some cur)
    (hmono : TaskState.retired before⊆TaskState.retired after)
    (w : HierarchyAddresses.Word depth) (i : Fin 8) (j : Fin (m+1))
    (hw : ∀ k : Fin depth,target ⟨k.val,by have := k.isLt; omega⟩=w k)
    (hi : target ⟨depth,by omega⟩=i) (hd : ¬TaskDisclosed after target j) :
    HiddenAt 0 (HiddenInner i j) depth w (planAt before after cur hc (0+depth)) := by
  have hn : target∉TaskState.retired after := fun h => hd (retired_all_tasks_disclosed h j)
  have hle : cur≤target := ((FrontierState.current_eq_some_iff _ _).mp hc).2 target (fun he => hn (hmono he))
  apply hiddenAt_plan_of_witness before after cur target hc hle 0 (HiddenInner i j) depth le_rfl w
  · intro k
    exact Fin.elim0 (Fin.cast (by omega) k)
  · intro k
    simpa only [Nat.sub_self,Nat.zero_add] using hw k
  · intro hp
    have hcur : currentChild cur 0=cur ⟨depth,by omega⟩ := by
      unfold currentChild
      congr 1
      apply Fin.ext
      simp
    have hnext : currentChild cur 0 ≤ i := by
      rw [hcur,← hi]
      apply coordinate_le_of_prefix cur target _ hle
      intro k hk
      exact hp ⟨k.val,by change k.val<depth at hk; omega⟩
    rcases lt_or_eq_of_le hnext with hl | he
    · exact Or.inl hl
    · refine Or.inr ⟨he,?_⟩
      have heq : cur=target := by
        funext k
        by_cases hk : k.val<depth
        · exact hp ⟨k.val,by omega⟩
        · have hk' : k=(⟨depth,by omega⟩ : Fin (0+depth+1)) := by
            apply Fin.ext
            change k.val=depth
            have := k.isLt
            omega
          rw [hk']
          exact hcur.symm.trans (he.trans hi.symm)
      apply decide_eq_false
      simpa only [heq] using hd

end GradientHessian.CensoredDirection
