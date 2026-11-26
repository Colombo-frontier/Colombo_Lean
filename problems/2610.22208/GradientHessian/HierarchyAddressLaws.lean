import GradientHessian.HierarchyAddresses
import GradientHessian.RawSubtreeFactor

/-! Compatibility and measurability of the genuine hierarchy addresses.
Raw projections are measurable under the actual recursive product spaces;
coefficient descendants use precisely the corresponding leaf slots. -/

noncomputable section
namespace GradientHessian.HierarchyAddresses

open Classical HigherHierarchy FrontierState

def prependSlot (h : ℕ) : (depth : ℕ) → Word depth → LeafSlot h → LeafSlot (h+depth)
  | 0,_,i => i
  | depth+1,w,i => (w 0,prependSlot h depth (Fin.tail w) i)

theorem prependSlot_prefix (h : ℕ) : ∀ depth (w : Word depth) (i : LeafSlot h) (j : Fin depth),
    leafWord (h+depth) (prependSlot h depth w i) (j.castLE (by omega))=w j
  | 0,_,_,j => Fin.elim0 j
  | depth+1,w,i,j => by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [leafWord,prependSlot]
    · simpa only [leafWord,prependSlot,Fin.cons_succ] using
        prependSlot_prefix h depth (Fin.tail w) i k

theorem prependSlot_in_subtree (h depth : ℕ) (w : Word depth) (i : LeafSlot h) :
    leafEquiv (h+depth) (prependSlot h depth w i) ∈
      subtree (node (h+depth) ⟨depth,by omega⟩ w) := by
  apply (node_mem_iff _ _ _ _).mpr
  exact prependSlot_prefix h depth w i

section Data
universe u
variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] theorem dataAt_zero (h : ℕ) (w : Word 0) (x : Data Y E H m h) : dataAt h 0 w x=x := rfl

@[simp] theorem dataAt_succ (h depth : ℕ) (w : Word (depth+1)) (x : Data Y E H m (h+depth+1)) :
    dataAt h (depth+1) w x=dataAt h depth (Fin.tail w) (x.children (w 0)) := rfl

theorem leafData_at (h : ℕ) : ∀ depth (w : Word depth) (x : Data Y E H m (h+depth)) (i : LeafSlot h),
    leafData (h+depth) x (prependSlot h depth w i)=leafData h (dataAt h depth w x) i
  | 0,_,_,_ => rfl
  | depth+1,w,x,i => leafData_at h depth (Fin.tail w) (x.children (w 0)) i

@[simp] theorem oldData_zero (w : Word 0) (x : Data Y E H m 0) : oldData 0 w x=x := rfl

theorem castData_children {a b : ℕ} (h : a=b) (x : Data Y E H m (a+1)) (i : Fin 8) :
    (castData (congrArg Nat.succ h) x).children i=castData h (x.children i) := by
  subst b
  rfl

theorem oldData_succ (t : ℕ) (w : Word (t+1)) (x : Data Y E H m (t+1)) :
    oldData (t+1) w x=oldData t (Fin.tail w) (x.children (w 0)) := by
  change dataAt 0 t (Fin.tail w)
      ((castData (congrArg Nat.succ (Nat.zero_add t).symm) x).children (w 0))=
    dataAt 0 t (Fin.tail w) (castData (Nat.zero_add t).symm (x.children (w 0)))
  rw [castData_children]

end Data

section Raw
variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}

@[simp] theorem rawAt_zero (h : ℕ) (w : Word 0) (x : RawHierarchy.Raw d n r J E H h) :
    rawAt h 0 w x=x := rfl

@[simp] theorem rawAt_succ (h depth : ℕ) (w : Word (depth+1))
    (x : RawHierarchy.Raw d n r J E H (h+depth+1)) :
    rawAt h (depth+1) w x=rawAt h depth (Fin.tail w) (x.1 (w 0)) := rfl

theorem rawAt_eq_selectedRaw (h : ℕ) : ∀ depth (w : Word depth)
    (x : RawHierarchy.Raw d n r J E H (h+depth)),
    rawAt h depth w x=RawSubtreeFactor.selectedRaw h depth w x
  | 0,_,_ => rfl
  | depth+1,w,x => rawAt_eq_selectedRaw h depth (Fin.tail w) (x.1 (w 0))

variable [MeasurableSpace E] [∀ h, MeasurableSpace (H h)]

theorem factor_target_rawAt (h depth : ℕ) (w : Word depth) (x : RawHierarchy.Raw d n r J E H (h+depth)) :
    (RawSubtreeFactor.factor h depth w x).1=rawAt h depth w x :=
  (RawSubtreeFactor.factor_target h depth w x).trans (rawAt_eq_selectedRaw h depth w x).symm

theorem castRaw_measurable {a b : ℕ} (h : a=b) :
    Measurable (castRaw (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h) := by
  subst b
  exact measurable_id

theorem rawAt_measurable (h : ℕ) : ∀ depth (w : Word depth),
    Measurable (rawAt (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w)
  | 0,_ => measurable_id
  | depth+1,w => by
    change Measurable (fun x : (Fin 8 → RawHierarchy.Raw d n r J E H (h+depth)) ×
        (Fin 8 → H (h+depth)) => rawAt h depth (Fin.tail w) (x.1 (w 0)))
    exact (rawAt_measurable h depth (Fin.tail w)).comp
      ((measurable_pi_apply (w 0)).comp measurable_fst)

theorem rawAtDepth_measurable (t : ℕ) (depth : Fin (t+1)) (w : Word depth.val) :
    Measurable (rawAtDepth (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t depth w) :=
  (rawAt_measurable _ _ w).comp (castRaw_measurable _)

theorem rawAtHeight_measurable (t h : ℕ) (hh : h≤t) (w : Word (t-h)) :
    Measurable (rawAtHeight (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t h hh w) :=
  (rawAt_measurable _ _ w).comp (castRaw_measurable _)

theorem localizedRaw_measurable (t : ℕ) (depth : Fin t) (w : Word depth.val) :
    Measurable (localizedRaw (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t depth w) :=
  (rawAt_measurable _ _ w).comp (castRaw_measurable _)

end Raw

end GradientHessian.HierarchyAddresses
