import Bilevel.ChiVirtualFine
import Bilevel.ChiFinePhysicalLocality
import Bilevel.ChiVirtualNodeValues

/-! Actual finest active atoms need the prospective column only on an
unfinished frontier. Fixed inactive atoms use only the old disclosed prefix. -/
noncomputable section
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ZeroChainSchedule

theorem active_piece_value_eq_retain (P : ChiFine.Parameters) (n k r s : ℕ)
    (hs : r≤s) (hnext : n<r ∨ r<s) (z : Space n)
    (hz : ∀ a : Fin (n+1),r≤a.val → |z a|≤P.β/4) :
    P.pieces n k z=P.pieces n k (retain n s z) := by
  apply value_eq_retain _ ((P.pieces_contDiff n k).differentiable (by norm_num)) _ z hz
  intro w hw a ha
  rcases hnext with hn|hn
  · have := a.isLt
    omega
  · exact P.pieces_gradient_support n k r w hw a (by omega)

theorem inactive_piece_value_eq_retain (P : ChiFine.Parameters) (n k r s : ℕ)
    (hk : k≤levels P.θ) (hs : r≤s) (z : Space n)
    (hz : ∀ a : Fin (n+1),r≤a.val → |z a|≤P.signalResolution) :
    P.inactivePiece n k z=P.inactivePiece n k (retain n s z) :=
  value_eq_retain _ ((P.inactivePiece_contDiff n k).differentiable (by norm_num))
    (fun w hw a ha => P.inactivePiece_gradient_support n k r hk w hw a (by omega)) z hz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def inactiveLeaf (D : Geometry E) (c θ τ : ℝ) (p j : ℕ) (I : List ℕ)
    (z : Space (D j I).n) : ℝ :=
  pieceLeaf D c θ p j I z-if p=levels θ then signalLeaf D τ j I z else 0

theorem actual_pieceLeaf_eq_virtual (D : Geometry E) (r s : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (c θ : ℝ) (j : ℕ) (I : List ℕ) (p : ℕ) (u : E)
    (hprefix : ∀ a : Fin ((D j I).n+1),a.val<s j I → columns j I a=(D j I).frame (basis a))
    (hell : 0≤(D j I).ell) (hh : 0<(D j I).width) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hrs : r j I≤s j I) (hnext : (D j I).n<r j I ∨ r j I<s j I)
    (hz : ∀ a : Fin ((D j I).n+1),r j I≤a.val → |(D j I).coordinates u a|≤(D j I).width/4) :
    pieceLeaf D c θ p j I ((D j I).coordinates u)=
      pieceLeaf D c θ p j I (readout (D j I).n (s j I) (D j I).radius (columns j I) u) := by
  rw [readout_eq_retained _ _ _ _ _ hprefix]
  let P : ChiFine.Parameters := ⟨(D j I).ell,(D j I).width,θ,c,hell,hh,hθ,hc,hcs⟩
  exact active_piece_value_eq_retain P (D j I).n p (r j I) (s j I) hrs hnext ((D j I).coordinates u) hz

theorem actual_inactiveLeaf_eq_virtual (D : Geometry E) (r s : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (c θ : ℝ) (j : ℕ) (I : List ℕ) (p : ℕ) (u : E)
    (hprefix : ∀ a : Fin ((D j I).n+1),a.val<s j I → columns j I a=(D j I).frame (basis a))
    (hell : 0≤(D j I).ell) (hh : 0<(D j I).width) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hp : p≤levels θ) (hrs : r j I≤s j I)
    (hz : ∀ a : Fin ((D j I).n+1),r j I≤a.val → |(D j I).coordinates u a|≤
      width c (D j I).width θ (levels θ)/8) :
    inactiveLeaf D c θ (width c (D j I).width θ (levels θ)/8) p j I ((D j I).coordinates u)=
      inactiveLeaf D c θ (width c (D j I).width θ (levels θ)/8) p j I
        (readout (D j I).n (s j I) (D j I).radius (columns j I) u) := by
  rw [readout_eq_retained _ _ _ _ _ hprefix]
  let P : ChiFine.Parameters := ⟨(D j I).ell,(D j I).width,θ,c,hell,hh,hθ,hc,hcs⟩
  exact inactive_piece_value_eq_retain P (D j I).n p (r j I) (s j I) hp hrs ((D j I).coordinates u) hz

end Bilevel.ChiPrefixEvaluation
