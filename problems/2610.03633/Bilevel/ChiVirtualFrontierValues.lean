import Bilevel.ChiVirtualSelectionValues
import Bilevel.ChiVirtualFineValues
import Bilevel.ChiFrontierAdvance

/-! Active fine evaluation follows the actual unfinished frontier. No
disclosure or value identity is required in future unselected branches. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiTreeProgress
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_select_eq_virtual_frontier (m : ℕ) (D : Geometry E)
    (r s : ℕ → List ℕ → ℕ) (columns : ∀ j I,Fin ((D j I).n+1) → E)
    (leaf : ∀ j I,Space (D j I).n → ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m E)
    (hprefix : ∀ k P,∀ a : Fin ((D k P).n+1),a.val<s k P → columns k P a=(D k P).frame (basis a))
    (hrs : ∀ k P,r k P≤s k P)
    (hh : ∀ k P,j≤k → k<j+d → 0<(D k P).width)
    (hblind : ∀ k P,j≤k → k<j+d → ∀ a : Fin ((D k P).n+1),
      r k P≤a.val → |(D k P).coordinates (block m k x) a|≤(D k P).width/4)
    (hfront : FrontierAdvance D r s d j I)
    (hleaf : ∀ P,FrontierAdvance D r s 0 (j+d) P →
      leaf (j+d) P ((D (j+d) P).coordinates (block m (j+d) x))=
      leaf (j+d) P (readout (D (j+d) P).n (s (j+d) P) (D (j+d) P).radius
        (columns (j+d) P) (block m (j+d) x))) :
    selectFamily m D (fun k P y => leaf k P ((D k P).coordinates (block m k y))) d j I x=
      virtualSelect D s columns leaf d j I (padded x) := by
  induction d generalizing j I with
  | zero => exact hleaf I hfront
  | succ d ih =>
    dsimp only [selectFamily,virtualSelect]
    apply Finset.sum_congr rfl
    intro i _
    change (D j I).selector i (block m j x)*_=virtualSelector (D j I) (s j I) (columns j I) i (block m j x)*_
    have hsel := actual_selector_eq_virtual (D j I) (s j I) (columns j I) (hprefix j I)
      (hh j I le_rfl (by omega)) i (block m j x)
      (fun a ha => hblind j I le_rfl (by omega) a ((hrs j I).trans ha))
    by_cases hi : i.val≤r j I
    · rw [hsel]
      congr 1
      apply ih (j+1) (child I i.val)
      · intro k P hk hkd
        exact hh k P (by omega) (by omega)
      · intro k P hk hkd
        exact hblind k P (by omega) (by omega)
      · exact hfront i hi
      · convert hleaf using 1
        rw [show j+1+d=j+(d+1) by omega]
    · have hz : (D j I).selector i (block m j x)=0 :=
        ChiCarrier.selector_future_zero (r j I) _ (fun a ha =>
          ZeroChainResidualScaled.scaled_coordinate_small (D j I).width (hh j I le_rfl (by omega))
            ((D j I).coordinates (block m j x)) a (hblind j I le_rfl (by omega) a ha)) i (by omega)
      rw [← hsel,hz,zero_mul,zero_mul]

theorem actual_selectedPiece_eq_virtual (m : ℕ) (D : Geometry E)
    (r s : ℕ → List ℕ → ℕ) (columns : ∀ j I,Fin ((D j I).n+1) → E)
    (d j : ℕ) (I : List ℕ) (x : Blocks m E)
    (hprefix : ∀ k P,∀ a : Fin ((D k P).n+1),a.val<s k P → columns k P a=(D k P).frame (basis a))
    (hrs : ∀ k P,r k P≤s k P)
    (hh : ∀ k P,j≤k → k≤j+d → 0<(D k P).width)
    (hblind : ∀ k P,j≤k → k≤j+d → ∀ a : Fin ((D k P).n+1),
      r k P≤a.val → |(D k P).coordinates (block m k x) a|≤(D k P).width/4)
    (hfront : FrontierAdvance D r s d j I)
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D (j+d) P).ell) (p : ℕ) :
    selectedFinePiece m D d j I c θ p x=virtualSelect D s columns (pieceLeaf D c θ p) d j I (padded x) := by
  apply actual_select_eq_virtual_frontier m D r s columns (pieceLeaf D c θ p) d j I x hprefix hrs
    (fun k P hk hkd => hh k P hk (by omega))
    (fun k P hk hkd => hblind k P hk (by omega)) hfront
  intro P hp
  exact actual_pieceLeaf_eq_virtual D r s columns c θ (j+d) P p (block m (j+d) x)
    (hprefix _ _) (hell P) (hh _ _ (by omega) le_rfl) hc hcs hθ (hrs _ _) hp
    (hblind _ _ (by omega) le_rfl)

end Bilevel.ChiPrefixEvaluation
