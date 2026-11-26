import Bilevel.ChiTreeProgressCounter

/-! A single terminal column suffices for the actual sequential tree counter.
Completed earlier subtrees release no further columns. The compatibility
predicate below is discharged by the concrete counter, rather than assumed
by the final canonical release theorem. -/
noncomputable section
namespace Bilevel.ChiTreeProgress
open ChiCarrier ChiRecursive ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def BudgetTree (D : Geometry E) (n : ℕ → ℕ) (r : ℕ → List ℕ → ℕ) :
    ℕ → ℕ → List ℕ → ℕ → Prop
  | 0,j,I,q => (D j I).n=n j ∧ r j I=nodePrefix n 0 j q
  | d+1,j,I,q => (D j I).n=n j ∧ r j I=nodePrefix n (d+1) j q ∧
      ∀ i : Fin ((D j I).n+1),BudgetTree D n r d (j+1) (child I i.val)
        (childBudget (capacity n d (j+1)) i.val q)

def nextRelease (D : Geometry E) (r : ℕ → List ℕ → ℕ) : ℕ → ℕ → List ℕ → E
  | 0,j,I => if h : r j I<(D j I).n+1 then (D j I).frame (basis ⟨r j I,h⟩) else 0
  | d+1,j,I => if r j I<(D j I).n+1 then nextRelease D r d (j+1) (child I (r j I)) else 0

theorem BudgetTree.completed {D : Geometry E} {n : ℕ → ℕ} {r : ℕ → List ℕ → ℕ}
    {d j q : ℕ} {I : List ℕ} (h : BudgetTree D n r d j I q)
    (hq : capacity n d j≤q) : CompletedLeaves D r d j I := by
  induction d generalizing j I q with
  | zero =>
    change (D j I).n<r j I
    rw [h.1,h.2,nodePrefix_complete n 0 j q hq]
    omega
  | succ d ih =>
    intro i
    apply ih (h.2.2 i)
    have hi : i.val<parentPrefix (n j+1) (capacity n d (j+1)) q := by
      change i.val<nodePrefix n (d+1) j q
      rw [nodePrefix_complete n (d+1) j q hq,←h.1]
      exact i.isLt
    exact (earlier_child_complete _ _ _ _ (capacity_pos n d (j+1)) hi).ge

theorem BudgetTree.frontier {D : Geometry E} {n : ℕ → ℕ} {r : ℕ → List ℕ → ℕ}
    {d j q : ℕ} {I : List ℕ} (h : BudgetTree D n r d j I q)
    (V : Submodule ℝ E) (hv : nextRelease D r d j I∈V) : FrontierKnown D r V d j I := by
  induction d generalizing j I q with
  | zero =>
    intro k hk
    have hr : r j I<(D j I).n+1 := by rw [←hk];exact k.isLt
    have he : (⟨r j I,hr⟩ : Fin ((D j I).n+1))=k := Fin.ext hk.symm
    simpa only [nextRelease,dif_pos hr,he] using hv
  | succ d ih =>
    apply frontierKnown_of_completed_children
    · intro i hi
      apply (h.2.2 i).completed
      rw [h.2.1] at hi
      exact (earlier_child_complete _ _ _ _ (capacity_pos n d (j+1)) hi).ge
    · intro i hi
      apply ih (h.2.2 i)
      simpa only [nextRelease,←hi,if_pos i.isLt] using hv

theorem canonical_budgetTree (D : Geometry E) (n : ℕ → ℕ)
    (hn : ∀ j I,(D j I).n=n j) (total q d j : ℕ) (I : List ℕ)
    (hI : I.length=j) (hd : j+d=total) :
    BudgetTree D n (counter n total q) d j I (nodeBudget n total 0 q I) := by
  induction d generalizing j I with
  | zero =>
    refine ⟨hn j I,?_⟩
    rw [counter_at n total q j I hI]
    congr 1; omega
  | succ d ih =>
    refine ⟨hn j I,?_,?_⟩
    · rw [counter_at n total q j I hI]
      congr 1; omega
    · intro i
      have hIc : (child I i.val).length=j+1 := by simp [child,hI]
      have hi' := ih (j+1) (child I i.val) hIc (by omega)
      have he : total-(j+1)=d := by omega
      simpa only [child,counter_child_budget n total q j I hI,he] using hi'

theorem canonical_frontier (D : Geometry E) (n : ℕ → ℕ)
    (hn : ∀ j I,(D j I).n=n j) (total q d j : ℕ) (I : List ℕ)
    (hI : I.length=j) (hd : j+d=total) (V : Submodule ℝ E)
    (hv : nextRelease D (counter n total q) d j I∈V) :
    FrontierKnown D (counter n total q) V d j I :=
  (canonical_budgetTree D n hn total q d j I hI hd).frontier V hv

end Bilevel.ChiTreeProgress
