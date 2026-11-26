import Bilevel.ChiVirtualFineValues

noncomputable section
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem virtualSelect_sub (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (f g : ∀ j I,Space (D j I).n → ℝ)
    (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    virtualSelect D r columns (fun j I z => f j I z-g j I z) d j I u=
      virtualSelect D r columns f d j I u-virtualSelect D r columns g d j I u := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih => simp only [virtualSelect,ih,mul_sub,Finset.sum_sub_distrib]

theorem virtualOuterLeaf_sub (m : ℕ) (M : Node E) (D : Geometry F) (rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (f g : ∀ j I,Space (D j I).n → ℝ)
    (d : ℕ) (z : Joint E (Blocks m F)) :
    virtualOuterLeaf m M D rM r macroColumns columns (fun j I z => f j I z-g j I z) d z=
      virtualOuterLeaf m M D rM r macroColumns columns f d z-
        virtualOuterLeaf m M D rM r macroColumns columns g d z := by
  simp only [virtualOuterLeaf,virtualSelect_sub,mul_sub,Finset.sum_sub_distrib]

theorem virtualOuterLeaf_inactive (m : ℕ) (M : Node E) (D : Geometry F) (rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (c θ τ : ℝ) (p d : ℕ) (z : Joint E (Blocks m F)) :
    virtualOuterLeaf m M D rM r macroColumns columns (inactiveLeaf D c θ τ p) d z=
      virtualOuterLeaf m M D rM r macroColumns columns (pieceLeaf D c θ p) d z-
        if p=levels θ then virtualOuterLeaf m M D rM r macroColumns columns (signalLeaf D τ) d z else 0 := by
  by_cases hp : p=levels θ
  · have he : inactiveLeaf D c θ τ p=fun j I z => pieceLeaf D c θ p j I z-signalLeaf D τ j I z := by
      funext j I z
      simp only [inactiveLeaf,if_pos hp]
    rw [he,virtualOuterLeaf_sub,if_pos hp]
  · have he : inactiveLeaf D c θ τ p=pieceLeaf D c θ p := by
      funext j I z
      simp only [inactiveLeaf,if_neg hp,sub_zero]
    rw [he,if_neg hp,sub_zero]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem weighted_last_sub (N : ℕ) (f w : ℕ → ℝ) (g : ℝ) :
    (∑ p ∈ Finset.range (N+1),(f p-if p=N then g else 0)*w p)=
      (∑ p ∈ Finset.range (N+1),f p*w p)-g*w N := by
  simp only [sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,Finset.sum_ite_eq',
    Finset.mem_range,Nat.lt_succ_self,if_true]

end Bilevel.ChiPrefixEvaluation
