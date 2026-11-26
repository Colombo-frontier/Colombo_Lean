import GradientHessian.RawSubtreeFactor

/-! Structural locality of a raw subtree factor. An unchanged external
factor preserves siblings and ancestor directions exactly; any relation
preserved by that assembly propagates from the selected subtree to the root. -/

noncomputable section
namespace GradientHessian.RawSubtreeLocality
open RawHierarchy RawSubtreeFactor

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

theorem rest_eq_child (h depth : ℕ) (w : Word (depth+1))
    (x y : Raw d n r J E H (h+depth+1))
    (he : (factor h (depth+1) w x).2=(factor h (depth+1) w y).2) :
    (factor h depth (Fin.tail w) (x.1 (w 0))).2=(factor h depth (Fin.tail w) (y.1 (w 0))).2 :=
  congrArg Prod.fst he

theorem rest_eq_sibling (h depth : ℕ) (w : Word (depth+1))
    (x y : Raw d n r J E H (h+depth+1))
    (he : (factor h (depth+1) w x).2=(factor h (depth+1) w y).2)
    (i : Fin 8) (hi : i≠w 0) : x.1 i=y.1 i := by
  obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq hi
  exact congrArg (fun z : Rest d n r J E H h (depth+1) => z.2.1 q) he

theorem rest_eq_directions (h depth : ℕ) (w : Word (depth+1))
    (x y : Raw d n r J E H (h+depth+1))
    (he : (factor h (depth+1) w x).2=(factor h (depth+1) w y).2) : x.2=y.2 :=
  congrArg (fun z : Rest d n r J E H h (depth+1) => z.2.2) he

/-- A literal path-local change: every off-path raw subtree and every
ancestor direction is identical. At the endpoint only `rel` is permitted. -/
def PathChange (h : ℕ) (rel : Raw d n r J E H h → Raw d n r J E H h → Prop) :
    (depth : ℕ) → Word depth → Raw d n r J E H (h+depth) → Raw d n r J E H (h+depth) → Prop
  | 0,_,x,y => rel x y
  | depth+1,w,x,y => x.2=y.2 ∧ (∀ i,i≠w 0 → x.1 i=y.1 i) ∧
      PathChange h rel depth (Fin.tail w) (x.1 (w 0)) (y.1 (w 0))

theorem pathChange_of_rest_eq (h : ℕ) (rel : Raw d n r J E H h → Raw d n r J E H h → Prop) :
    ∀ depth (w : Word depth) (x y : Raw d n r J E H (h+depth)),
      (factor h depth w x).2=(factor h depth w y).2 →
      rel (selectedRaw h depth w x) (selectedRaw h depth w y) → PathChange h rel depth w x y
  | 0,_w,_x,_y,_he,hr => hr
  | depth+1,w,x,y,he,hr => ⟨rest_eq_directions h depth w x y he,
      rest_eq_sibling h depth w x y he,
      pathChange_of_rest_eq h rel depth (Fin.tail w) _ _ (rest_eq_child h depth w x y he) hr⟩

theorem lift_relation (Rel : (t : ℕ) → Raw d n r J E H t → Raw d n r J E H t → Prop)
    (hrefl : ∀ t x, Rel t x x)
    (hstep : ∀ t (x y : Raw d n r J E H (t+1)),
      (∀ i, Rel t (x.1 i) (y.1 i)) → x.2=y.2 → Rel (t+1) x y) (h : ℕ) :
    ∀ depth (w : Word depth) (x y : Raw d n r J E H (h+depth)),
      (factor h depth w x).2=(factor h depth w y).2 →
      Rel h (selectedRaw h depth w x) (selectedRaw h depth w y) → Rel (h+depth) x y
  | 0,_w,_x,_y,_he,hr => hr
  | depth+1,w,x,y,he,hr => by
    apply hstep (h+depth) x y _ (rest_eq_directions h depth w x y he)
    intro i
    by_cases hi : i=w 0
    · subst i
      exact lift_relation Rel hrefl hstep h depth (Fin.tail w) _ _
        (rest_eq_child h depth w x y he) hr
    · rw [rest_eq_sibling h depth w x y he i hi]
      exact hrefl _ _

theorem rest_eq_other_subtree (h : ℕ) : ∀ depth (w q : Word depth)
    (x y : Raw d n r J E H (h+depth)),
    (factor h depth w x).2=(factor h depth w y).2 → q≠w →
      selectedRaw h depth q x=selectedRaw h depth q y
  | 0,w,q,_x,_y,_he,hq => False.elim (hq (Subsingleton.elim q w))
  | depth+1,w,q,x,y,he,hq => by
    by_cases hh : q 0=w 0
    · have ht : Fin.tail q≠Fin.tail w := by
        intro ht
        apply hq
        rw [← Fin.cons_self_tail q,← Fin.cons_self_tail w,hh,ht]
      change selectedRaw h depth (Fin.tail q) (x.1 (q 0))=
        selectedRaw h depth (Fin.tail q) (y.1 (q 0))
      rw [hh]
      exact rest_eq_other_subtree h depth (Fin.tail w) (Fin.tail q) _ _
        (rest_eq_child h depth w x y he) ht
    · change selectedRaw h depth (Fin.tail q) (x.1 (q 0))=
        selectedRaw h depth (Fin.tail q) (y.1 (q 0))
      rw [rest_eq_sibling h depth w x y he (q 0) hh]

def replace (h depth : ℕ) (w : Word depth) (z : Raw d n r J E H h)
    (x : Raw d n r J E H (h+depth)) : Raw d n r J E H (h+depth) :=
  (factor h depth w).symm (z,(factor h depth w x).2)

theorem factor_replace (h depth : ℕ) (w : Word depth) (z : Raw d n r J E H h)
    (x : Raw d n r J E H (h+depth)) :
    factor h depth w (replace h depth w z x)=(z,(factor h depth w x).2) :=
  (factor h depth w).apply_symm_apply _

theorem replace_target (h depth : ℕ) (w : Word depth) (z : Raw d n r J E H h)
    (x : Raw d n r J E H (h+depth)) : selectedRaw h depth w (replace h depth w z x)=z := by
  rw [← factor_target,factor_replace]

theorem replace_other_subtree (h depth : ℕ) (w q : Word depth) (hq : q≠w)
    (z : Raw d n r J E H h) (x : Raw d n r J E H (h+depth)) :
    selectedRaw h depth q (replace h depth w z x)=selectedRaw h depth q x :=
  rest_eq_other_subtree h depth w q _ _
    (by simpa only using congrArg Prod.snd (factor_replace h depth w z x)) hq

end GradientHessian.RawSubtreeLocality
