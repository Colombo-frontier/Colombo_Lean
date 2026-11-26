import GradientHessian.FrontierState

/-! Lexicographic order and the laminar geometry of the actual finite tree.
Earlier children of the current branch are retired, with no assertion that
their scalar ports equal one at an arbitrary physical point. -/

noncomputable section
namespace GradientHessian.FrontierOrder

open Classical FrontierState

variable {L : ℕ}

theorem children_order (v : Node L) (hv : v.1.val < L) {i j : Fin 8} (hij : i<j)
    {a b : Leaf L} (ha : a ∈ subtree (child v hv i)) (hb : b ∈ subtree (child v hv j)) : a<b := by
  have ha' := (inSubtree_child_iff v hv i a).mp ((mem_subtree _ _).mp ha)
  have hb' := (inSubtree_child_iff v hv j b).mp ((mem_subtree _ _).mp hb)
  change ∃ k : Fin L,(∀ l,l<k → a l=b l) ∧ a k<b k
  refine ⟨⟨v.1.val,hv⟩,?_,?_⟩
  · intro l hl
    have hlt : l.val<v.1.val := hl
    have h₁ := ha'.1 ⟨l.val,hlt⟩
    have h₂ := hb'.1 ⟨l.val,hlt⟩
    exact h₁.trans h₂.symm
  · simpa only [ha'.2,hb'.2] using hij

theorem earlier_children_retired (R : Retired L) (v : Node L) (hv : v.1.val<L)
    {cur : Leaf L} (hc : current R=some cur) {j : Fin 8}
    (hj : cur ∈ subtree (child v hv j)) : ∀ i : Fin 8,i<j → subtree (child v hv i) ⊆ R := by
  intro i hij leaf hl
  by_contra hn
  have hmin := ((current_eq_some_iff R cur).mp hc).2 leaf hn
  exact (not_le_of_gt (children_order v hv hij hl hj)) hmin

theorem current_child (R : Retired L) (v : Node L) (hv : v.1.val<L)
    {cur : Leaf L} (hc : current R=some cur) (hcur : cur ∈ subtree v) :
    ∃ j : Fin 8,cur ∈ subtree (child v hv j) ∧
      (subtree (child v hv j) \ R).Nonempty ∧
      ∀ i : Fin 8,i<j → subtree (child v hv i) ⊆ R := by
  let j := cur ⟨v.1.val,hv⟩
  have hj : cur ∈ subtree (child v hv j) :=
    (mem_subtree _ _).mpr ((inSubtree_child_iff v hv j cur).mpr ⟨(mem_subtree _ _).mp hcur,rfl⟩)
  exact ⟨j,hj,⟨cur,Finset.mem_sdiff.mpr ⟨hj,((current_eq_some_iff R cur).mp hc).1⟩⟩,
    earlier_children_retired R v hv hc hj⟩

theorem subtree_subset_of_common_leaf (v w : Node L) (hd : v.1.val≤w.1.val)
    {common : Leaf L} (hv : common ∈ subtree v) (hw : common ∈ subtree w) :
    subtree w ⊆ subtree v := by
  intro leaf hl
  apply (mem_subtree _ _).mpr
  intro i
  have hh := ((mem_subtree w common).mp hw) (i.castLE hd)
  have hlh := ((mem_subtree w leaf).mp hl) (i.castLE hd)
  have hvh := ((mem_subtree v common).mp hv) i
  exact hlh.trans (hh.symm.trans hvh)

theorem overlapping_subtrees_nested (v w : Node L)
    {common : Leaf L} (hv : common ∈ subtree v) (hw : common ∈ subtree w) :
    subtree v ⊆ subtree w ∨ subtree w ⊆ subtree v := by
  rcases le_total v.1.val w.1.val with h | h
  · exact Or.inr (subtree_subset_of_common_leaf v w h hv hw)
  · exact Or.inl (subtree_subset_of_common_leaf w v h hw hv)

theorem subtrees_disjoint_or_nested (v w : Node L) :
    Disjoint (subtree v) (subtree w) ∨ subtree v ⊆ subtree w ∨ subtree w ⊆ subtree v := by
  by_cases h : Disjoint (subtree v) (subtree w)
  · exact Or.inl h
  · obtain ⟨leaf,hv,hw⟩ := Finset.not_disjoint_iff.mp h
    exact Or.inr (overlapping_subtrees_nested v w hv hw)

theorem current_in_last_child_all_retired (R S : Retired L) (hRS : R ⊆ S)
    (v : Node L) (hv : v.1.val<L) {cur : Leaf L} (hc : current R=some cur)
    (hcur : cur ∈ subtree (child v hv (Fin.last 7)))
    (hlast : subtree (child v hv (Fin.last 7)) ⊆ S) : subtree v ⊆ S := by
  rw [subtree_eq_children v hv]
  intro leaf hl
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hl
  by_cases he : i=Fin.last 7
  · subst i
    exact hlast hi
  · have hlt : i<Fin.last 7 := by have := i.isLt; change i.val<7; apply lt_of_le_of_ne (by omega); exact fun h => he (Fin.ext h)
    exact hRS (earlier_children_retired R v hv hc hcur i hlt hi)

end GradientHessian.FrontierOrder
