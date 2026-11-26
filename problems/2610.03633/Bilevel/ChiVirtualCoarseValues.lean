import Bilevel.ChiVirtualSelectionValues
import Bilevel.ChiVirtualMacroValues

/-! Exact original/disclosed equality for every coarse normal carrier,
including the deepest centered carrier and one-sided macro selector. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiExtensionCalibration PrimitiveGeometry
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
  (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
  (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
  (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<r j I → columns j I k=(D j I).frame (basis k))
  (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width)
  (z : Joint E (Blocks m F))
  (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
  (hblind : ∀ j I,j≤J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
    |(D j I).coordinates (block m j z.snd) k|≤(D j I).width/4)

include hmPrefix hprefix hmw hh hmBlind hblind

theorem actual_outerClosed_eq_virtual (t : ℕ) (ht : t<J)
    (hhp : ∀ I,0<(D (t+1) I).parentWidth)
    (hw : ∀ I,(D (t+1) I).width≤(D (t+1) I).parentWidth)
    (hfuture : ∀ I,∀ i : Fin ((D t I).n+1),r t I ≤ i.val →
      r (t+1) (child I i.val)≤(D (t+1) (child I i.val)).n) :
    outerCarrier m M D J t z=virtualOuterCarrier m M D rM r macroColumns columns J t z := by
  unfold outerCarrier outerSelected virtualOuterCarrier
  apply Finset.sum_congr rfl
  intro i _
  change wrappedSelector M i z.fst*jointCarrier m D J 0 [i.val] t z.snd=_
  rw [actual_outerSelector_eq_virtual M rM macroColumns hmPrefix hmw i z.fst hmBlind]
  congr 1
  have he : J-t-1+1+t=J := by omega
  rw [← he]
  exact actual_selectedClosed_eq_virtual D r columns (J-t-1) t 0 [i.val] (padded z.snd) hprefix
    (fun k P _ hk => hh k P (by omega))
    (fun k P _ hk => hblind k P (by omega))
    (by simpa only [Nat.zero_add] using hhp) (by simpa only [Nat.zero_add] using hw)
    (by convert hfuture using 1; rw [Nat.zero_add])

theorem actual_outerDeepest_eq_virtual :
    outerDeepestA m M D J z=
      virtualOuterCarrier m M D rM r macroColumns columns J J z-
        virtualOuterLeaf m M D rM r macroColumns columns (frontierLeaf D) J z := by
  unfold outerDeepestA outerCarrier outerFineFrontier outerSelected virtualOuterCarrier virtualOuterLeaf
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change wrappedSelector M i z.fst*jointCarrier m D J 0 [i.val] J z.snd-
    wrappedSelector M i z.fst*selectedFineFrontier m D J 0 [i.val] z.snd=_
  rw [← mul_sub,actual_outerSelector_eq_virtual M rM macroColumns hmPrefix hmw i z.fst hmBlind]
  have hi := actual_deepest_eq_virtual m D r columns J 0 [i.val] z.snd hprefix
    (fun k P _ hk => hh k P (by omega)) (fun k P _ hk => hblind k P (by omega))
  change jointCarrier m D J 0 [i.val] J z.snd-selectedFineFrontier m D J 0 [i.val] z.snd=_ at hi
  rw [hi,mul_sub]

theorem actual_coarse_eq_virtual
    (hhp : ∀ t,t<J → ∀ I,0<(D (t+1) I).parentWidth)
    (hw : ∀ t,t<J → ∀ I,(D (t+1) I).width≤(D (t+1) I).parentWidth)
    (hfuture : ∀ t,t<J → ∀ I,∀ i : Fin ((D t I).n+1),r t I ≤ i.val →
      r (t+1) (child I i.val)≤(D (t+1) (child I i.val)).n) (i : Fin J) :
    coarseFamily m M D J i z=virtualCoarse m M D rM r macroColumns columns J i z := by
  unfold coarseFamily virtualCoarse
  split_ifs with he
  · exact actual_outerDeepest_eq_virtual m M D J rM r macroColumns columns hmPrefix hprefix hmw hh z hmBlind hblind
  · have ht : i.val+1<J := by have := i.isLt;omega
    exact actual_outerClosed_eq_virtual m M D J rM r macroColumns columns hmPrefix hprefix hmw hh z hmBlind hblind
      (i.val+1) ht (hhp _ ht) (hw _ ht) (hfuture _ ht)

end Bilevel.ChiPrefixEvaluation
