import Bilevel.ChiTreeRelease

/-! Numeric retained-prefix certificate for active source evaluation.
Only reachable old-prefix children are required. -/
noncomputable section
namespace Bilevel.ChiTreeProgress
open ChiCarrier ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def FrontierAdvance (D : Geometry E) (old new : ℕ → List ℕ → ℕ) : ℕ → ℕ → List ℕ → Prop
  | 0,j,I => (D j I).n < old j I ∨ old j I < new j I
  | d+1,j,I => ∀ i : Fin ((D j I).n+1), i.val ≤ old j I →
      FrontierAdvance D old new d (j+1) (child I i.val)

theorem completed_frontierAdvance {D : Geometry E} {old new : ℕ → List ℕ → ℕ}
    {d j : ℕ} {I : List ℕ} (h : CompletedLeaves D old d j I) :
    FrontierAdvance D old new d j I := by
  induction d generalizing j I with
  | zero => exact Or.inl h
  | succ d ih => exact fun i _ => ih (h i)

theorem BudgetTree.frontierAdvance {D : Geometry E} {n : ℕ → ℕ} {old new : ℕ → List ℕ → ℕ}
    {d j q : ℕ} {I : List ℕ} (ho : BudgetTree D n old d j I q)
    (hn : BudgetTree D n new d j I (q+1)) : FrontierAdvance D old new d j I := by
  induction d generalizing j I q with
  | zero =>
    change (D j I).n < old j I ∨ old j I < new j I
    rw [ho.1,ho.2,hn.2]
    simp only [nodePrefix]
    omega
  | succ d ih =>
    intro i hi
    rcases lt_or_eq_of_le hi with hi|hi
    · apply completed_frontierAdvance
      apply (ho.2.2 i).completed
      rw [ho.2.1] at hi
      exact (earlier_child_complete _ _ _ _ (capacity_pos n d (j+1)) hi).ge
    · have he : i.val = q / capacity n d (j+1) := by
        have hlt : i.val < n j+1 := by rw [← ho.1]; exact i.isLt
        rw [ho.2.1] at hi
        change i.val = min (n j+1) (q / capacity n d (j+1)) at hi
        omega
      have hh := hn.2.2 i
      rw [childBudget_success _ _ _ (capacity_pos n d (j+1)),if_pos he] at hh
      exact ih (ho.2.2 i) hh

end Bilevel.ChiTreeProgress
