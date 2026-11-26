import Bilevel.EndpointTransportVirtualLeaves
import Bilevel.ChiVirtualClosedValues

/-! The actual last ordinary parent is prefix-evaluable only after its
frontier is combined with the physical child release correction. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation

theorem lastParentCarrier_eq_virtual {m n D : ℕ} (Q : Rotations n D) (j : ℕ)
    (N : Node (Block D)) (kids : Fin (N.n+1) → Node (Block D))
    (r : ℕ) (rc : Fin (N.n+1) → ℕ) (columns : Fin (N.n+1) → Block D)
    (targets : ∀ i : Fin (N.n+1),Fin ((kids i).n+1) → Physical n D)
    (hc : ∀ k : Fin (N.n+1),k.val<r → columns k=N.frame (basis k))
    (ht : ∀ i,∀ k : Fin ((kids i).n+1),k.val<rc i →
      targets i k=endpointFrame Q (kids i).frame (Fin.last (n+1)) (basis k))
    (hh : 0<N.width) (hhp : ∀ i,0<(kids i).parentWidth)
    (hw : ∀ i,(kids i).width≤(kids i).parentWidth)
    (x : HybridTangent (Blocks m (Block D)) n D)
    (hb : ∀ k : Fin (N.n+1),r≤k.val → |N.coordinates (block m j x.fst) k|≤N.width/4)
    (hbt : ∀ i,∀ k : Fin ((kids i).n+1),rc i≤k.val →
      |(physicalCoordinates Q (kids i) x.snd).snd k|≤(kids i).width/4)
    (hfuture : ∀ i : Fin (N.n+1),r ≤ i.val → rc i≤(kids i).n) :
    lastParentCarrier m j N kids jointFstLinear jointSndLinear Q x=
      virtualH N r columns (block m j x.fst)+
        ∑ i : Fin (N.n+1),virtualResidual N r columns i (block m j x.fst)*
          (prefixPhysicalRelease (kids i) (rc i) (targets i) x.snd-1) := by
  let q : Fin (N.n+1) → ℝ := fun i => physicalRelease Q (kids i) x.snd
  have hq (i : Fin (N.n+1)) (hi : r ≤ i.val) : q i=0 :=
    ((targetNode Q (kids i)).release_flat_of_blind_terminal (hhp i) (hw i) x.snd
      (hbt i (Fin.last (kids i).n) (by simpa only [Fin.val_last] using hfuture i hi))).1
  have he := actual_closed_eq_virtual N r columns hc hh q hq (block m j x.fst) hb
  have hleft : lastParentCarrier m j N kids jointFstLinear jointSndLinear Q x=
      N.closed q (block m j x.fst) := by
    simp only [lastParentCarrier,physicalReleaseCorrection,jointH,jointResidual,Function.comp_apply,
      Node.closed,mul_sub,mul_one,Finset.sum_sub_distrib]
    change N.H (block m j x.fst)+((∑ i,N.residual i (block m j x.fst)*q i)-
      ∑ i,N.residual i (block m j x.fst))=
      N.H (block m j x.fst)-(∑ i,N.residual i (block m j x.fst))+
        ∑ i,N.residual i (block m j x.fst)*q i
    ring
  rw [hleft,he]
  have hqv (i : Fin (N.n+1)) : q i=prefixPhysicalRelease (kids i) (rc i) (targets i) x.snd :=
    physicalRelease_eq_prefix Q (kids i) (rc i) (targets i) (ht i) (hhp i) (hw i) x.snd (hbt i)
  simp only [virtualClosed,hqv,mul_sub,mul_one,Finset.sum_sub_distrib]
  ring

end Bilevel.EndpointTransportResponse

