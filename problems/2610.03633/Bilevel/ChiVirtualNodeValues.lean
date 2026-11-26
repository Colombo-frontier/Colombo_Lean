import Bilevel.ChiVirtualNode
import Bilevel.ChiCarrierPrefixEvaluation

/-! Construction-specific original-to-disclosed scalar equalities for
selectors, terminal release and closed/centered carriers. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def virtualClosed (D : Node E) (s : ℕ) (columns : Fin (D.n+1) → E)
    (q : Fin (D.n+1) → ℝ) (u : E) : ℝ :=
  virtualH D s columns u-(∑ i,virtualResidual D s columns i u)+
    ∑ i,virtualResidual D s columns i u*q i

theorem actual_selector_eq_virtual (D : Node E) (s : ℕ) (columns : Fin (D.n+1) → E)
    (hprefix : ∀ k : Fin (D.n+1),k.val<s → columns k=D.frame (basis k))
    (hh : 0<D.width) (i : Fin (D.n+1)) (u : E)
    (hz : ∀ k : Fin (D.n+1),s≤k.val → |D.coordinates u k|≤D.width/4) :
    D.selector i u=virtualSelector D s columns i u := by
  unfold virtualSelector
  rw [readout_eq_retained D.n s D.radius columns D.frame hprefix]
  exact selector_prefix_value D.n s D.width hh i (D.coordinates u) hz

theorem actual_release_eq_virtual (D : Node E) (s : ℕ) (columns : Fin (D.n+1) → E)
    (hprefix : ∀ k : Fin (D.n+1),k.val<s → columns k=D.frame (basis k))
    (hhp : 0<D.parentWidth) (hw : D.width≤D.parentWidth) (u : E)
    (hz : ∀ k : Fin (D.n+1),s≤k.val → |D.coordinates u k|≤D.width/4) :
    D.release u=virtualRelease D s columns u := by
  unfold virtualRelease
  rw [readout_eq_retained D.n s D.radius columns D.frame hprefix]
  change D.release u=releaseGate (retain D.n s (D.coordinates u) (Fin.last D.n)/D.parentWidth)
  rw [retain_apply]
  simp only [Fin.val_last]
  by_cases hn : D.n<s
  · rw [if_pos hn]
    rfl
  · rw [if_neg hn,zero_div,releaseGate_zero (by norm_num : (0:ℝ)≤1)]
    exact (D.release_flat_of_blind_terminal hhp hw u (hz (Fin.last D.n) (by simpa using Nat.le_of_not_gt hn))).1

omit [CompleteSpace E] in
theorem virtualClosed_formula (D : Node E) (s : ℕ) (columns : Fin (D.n+1) → E)
    (q : Fin (D.n+1) → ℝ) (u : E) :
    virtualClosed D s columns q u=
      closedCarrier D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius q
        (readout D.n s D.radius columns u) := by
  simp only [virtualClosed,virtualH,virtualResidual,closedCarrier,payloadCarrier,← R_eq_sum]

theorem actual_closed_eq_virtual (D : Node E) (s : ℕ) (columns : Fin (D.n+1) → E)
    (hprefix : ∀ k : Fin (D.n+1),k.val<s → columns k=D.frame (basis k))
    (hh : 0<D.width) (q : Fin (D.n+1) → ℝ) (hq : ∀ i,s ≤ i.val → q i=0)
    (u : E) (hz : ∀ k : Fin (D.n+1),s≤k.val → |D.coordinates u k|≤D.width/4) :
    D.closed q u=virtualClosed D s columns q u := by
  rw [D.closed_formula,virtualClosed_formula,readout_eq_retained D.n s D.radius columns D.frame hprefix]
  exact closedCarrier_prefix_value D.n s D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
    hh q hq (D.coordinates u) hz

theorem actual_centered_eq_virtual (D : Node E) (s : ℕ) (columns : Fin (D.n+1) → E)
    (hprefix : ∀ k : Fin (D.n+1),k.val<s → columns k=D.frame (basis k))
    (hh : 0<D.width) (u : E)
    (hz : ∀ k : Fin (D.n+1),s≤k.val → |D.coordinates u k|≤D.width/4) :
    D.H u-ChiFine.frontier D.n D.ell D.width (D.coordinates u)=
      virtualH D s columns u-ChiFine.frontier D.n D.ell D.width (readout D.n s D.radius columns u) := by
  unfold virtualH
  rw [readout_eq_retained D.n s D.radius columns D.frame hprefix]
  exact centeredPayload_prefix_value D.n s D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
    hh (D.coordinates u) hz

theorem actual_zero_eq_virtual (D : Node E) (s : ℕ) (columns : Fin (D.n+1) → E) :
    D.H 0=virtualH D s columns 0 := by
  simp [Node.H,virtualH,Node.coordinates_zero,readout,RadialWrapper.compress]

end Bilevel.ChiPrefixEvaluation
