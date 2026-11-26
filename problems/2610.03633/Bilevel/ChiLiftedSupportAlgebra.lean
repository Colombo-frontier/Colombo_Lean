import Bilevel.ChiLiftedFrontierSupport

/-! Actual lifted selector recursion preserves a known gradient subspace
when every terminal leaf is already supported. This is the coarse case,
which requires no extra frontier column. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiLiftedCarrier
open ChiBoundedChain ChiRecursive ChiCarrier
variable {E X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem selectFamily_gradient_mem {m : ℕ} (D : Geometry E) (A : X →L[ℝ] Blocks m E)
    (leaf : ℕ → List ℕ → X → ℝ) (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P))
    (d j : ℕ) (I : List ℕ) (W : Submodule ℝ X) (x : X)
    (hsel : ∀ k P,j≤k → k<j+d → ∀ i : Fin ((D k P).n+1),
      gradient (selector m k (D k P) A i) x∈W)
    (hbase : ∀ P,gradient (leaf (j+d) P) x∈W) :
    gradient (selectFamily m D A leaf d j I) x∈W := by
  induction d generalizing j I with
  | zero => exact hbase I
  | succ d ih =>
    change gradient (fun y => ∑ i : Fin ((D j I).n+1),selector m j (D j I) A i y*
      selectFamily m D A leaf d (j+1) (child I i.val) y) x∈W
    apply gradient_sum_mem Finset.univ W _
      (fun i => (selector_contDiff m j (D j I) A i 3).mul
        (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val)))
    intro i _
    apply gradient_mul_mem W (selector_contDiff m j (D j I) A i 3)
      (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val)) x (hsel j I le_rfl (by omega) i)
    apply ih (j+1) (child I i.val)
    · exact fun k P hk hkd a => hsel k P (by omega) (by omega) a
    · intro P
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbase P

end Bilevel.ChiLiftedCarrier
