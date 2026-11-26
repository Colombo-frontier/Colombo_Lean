import Bilevel.ChiTreeRelease

/-! Exact single-column disclosure and a concrete enlarged known space.
At completion there is no further disclosure; otherwise the released vector
is the next column of one actual terminal frame. -/
noncomputable section
namespace Bilevel.ChiTreeProgress
open ChiCarrier ChiRecursive ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BudgetTree.nextRelease_zero {D : Geometry E} {n : ℕ → ℕ} {r : ℕ → List ℕ → ℕ}
    {d j q : ℕ} {I : List ℕ} (h : BudgetTree D n r d j I q)
    (hq : capacity n d j≤q) : nextRelease D r d j I=0 := by
  cases d with
  | zero =>
    have hr : ¬r j I<(D j I).n+1 := by
      rw [h.1,h.2,nodePrefix_complete n 0 j q hq]
      omega
    exact dif_neg hr
  | succ d =>
    have hr : ¬r j I<(D j I).n+1 := by
      rw [h.1,h.2.1,nodePrefix_complete n (d+1) j q hq]
      omega
    exact if_neg hr

theorem BudgetTree.nextRelease_column {D : Geometry E} {n : ℕ → ℕ} {r : ℕ → List ℕ → ℕ}
    {d j q : ℕ} {I : List ℕ} (h : BudgetTree D n r d j I q)
    (hq : q<capacity n d j) :
    ∃ level P,∃ k : Fin ((D level P).n+1),level=j+d ∧ P.length=I.length+d ∧
      k.val=r level P ∧ nextRelease D r d j I=(D level P).frame (basis k) := by
  induction d generalizing j I q with
  | zero =>
    have hr : r j I<(D j I).n+1 := by
      rw [h.1,h.2]
      exact Nat.lt_succ_of_le (nodePrefix_incomplete n 0 j q hq)
    exact ⟨j,I,⟨r j I,hr⟩,by omega,by omega,rfl,dif_pos hr⟩
  | succ d ih =>
    have hr : r j I<(D j I).n+1 := by
      rw [h.1,h.2.1]
      exact Nat.lt_succ_of_le (nodePrefix_incomplete n (d+1) j q hq)
    let i : Fin ((D j I).n+1) := ⟨r j I,hr⟩
    have hq' : childBudget (capacity n d (j+1)) i.val q<capacity n d (j+1) := by
      apply future_child_incomplete (n j+1) _ _ i.val (capacity_pos n d (j+1))
      · rw [←h.1];exact i.isLt
      · exact h.2.1.symm.le
    obtain ⟨level,P,k,hl,hP,hk,he⟩ := ih (h.2.2 i) hq'
    refine ⟨level,P,k,by omega,?_,hk,?_⟩
    · simp only [child,List.length_append,List.length_singleton] at hP
      omega
    · simpa only [nextRelease,if_pos hr] using he

def enlargedSpace (V : Submodule ℝ E) (v : E) : Submodule ℝ E := V ⊔ Submodule.span ℝ {v}

theorem enlargedSpace_contains_old (V : Submodule ℝ E) (v : E) : V≤enlargedSpace V v := le_sup_left

theorem enlargedSpace_contains_release (V : Submodule ℝ E) (v : E) : v∈enlargedSpace V v :=
  (show Submodule.span ℝ {v}≤enlargedSpace V v from le_sup_right)
    (Submodule.subset_span (Set.mem_singleton v))

theorem canonical_single_release (D : Geometry E) (n : ℕ → ℕ)
    (hn : ∀ j I,(D j I).n=n j) (total q d j : ℕ) (I : List ℕ)
    (hI : I.length=j) (hd : j+d=total) (V : Submodule ℝ E) :
    FrontierKnown D (counter n total q)
      (enlargedSpace V (nextRelease D (counter n total q) d j I)) d j I :=
  canonical_frontier D n hn total q d j I hI hd _ (enlargedSpace_contains_release V _)

end Bilevel.ChiTreeProgress
