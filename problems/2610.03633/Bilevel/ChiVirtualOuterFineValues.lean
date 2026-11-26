import Bilevel.ChiVirtualFrontierValues
import Bilevel.ChiVirtualMacroValues

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiTreeProgress PrimitiveGeometry
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem outer_selector_future_zero (n r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) (i : Fin (n+1)) (hi : r < i.val) :
    ChiOuter.selector n i z=0 := by
  rcases ChiOuter.selector_jet_cases n i z with h|h
  · exact h.1
  · rw [h.1]
    exact ChiCarrier.selector_future_zero r z hz i hi

theorem actual_outerFinePiece_eq_virtual (m : ℕ) (M : Node E) (D : Geometry F) (J rM sM : ℕ)
    (r s : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<sM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<s j I → columns j I k=(D j I).frame (basis k))
    (hms : rM≤sM) (hrs : ∀ j I,r j I≤s j I)
    (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width)
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ j I,j≤J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
      |(D j I).coordinates (block m j z.snd) k|≤(D j I).width/4)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance D r s J 0 [i.val])
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ I,0≤(D J I).ell) (p : ℕ) :
    outerFinePiece m M D J c θ p z=
      virtualOuterLeaf m M D sM s macroColumns columns (pieceLeaf D c θ p) J z := by
  unfold outerFinePiece outerSelected virtualOuterLeaf
  apply Finset.sum_congr rfl
  intro i _
  change wrappedSelector M i z.fst*selectedFinePiece m D J 0 [i.val] c θ p z.snd=_
  have hsel := actual_outerSelector_eq_virtual M sM macroColumns hmPrefix hmw i z.fst
    (fun k hk => hmBlind k (hms.trans hk))
  by_cases hi : i.val≤rM
  · rw [hsel]
    congr 1
    exact actual_selectedPiece_eq_virtual m D r s columns J 0 [i.val] z.snd hprefix hrs
      (fun j I _ hj => hh j I (by omega)) (fun j I _ hj => hblind j I (by omega)) (hfront i hi)
      c θ hc hcs hθ (by simpa only [Nat.zero_add] using hell) p
  · have hz : wrappedSelector M i z.fst=0 :=
      outer_selector_future_zero M.n rM _ (fun k hk =>
        ZeroChainResidualScaled.scaled_coordinate_small M.width hmw (M.coordinates z.fst) k (hmBlind k hk)) i (by omega)
    rw [← hsel,hz,zero_mul,zero_mul]

end Bilevel.ChiPrefixEvaluation
