import Bilevel.EndpointTransportVirtualFormula
import Bilevel.ChiSplitFlexiblePrefix
import Bilevel.ChiVirtualNodeValues

/-! Exact physical leaf evaluation for independent endpoint prefix counts.
Centered leaves need no new source column; fine leaves require it only if
unfinished. The target release uses old target columns alone. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation RadialWrapper

theorem prefixPhysicalCoordinatesAt_eq_retained {n D : ℕ} (Q : Rotations n D)
    (N : Node (Block D)) (rs rt : ℕ) (S T : Fin (N.n+1) → Physical n D)
    (hs : ∀ k : Fin (N.n+1),k.val<rs → S k=endpointFrame Q N.frame 0 (basis k))
    (ht : ∀ k : Fin (N.n+1),k.val<rt → T k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))
    (Y : Physical n D) :
    prefixPhysicalCoordinatesAt N rs rt S T Y=
      pack (retain N.n rs (physicalCoordinates Q N Y).fst) (retain N.n rt (physicalCoordinates Q N Y).snd) := by
  unfold prefixPhysicalCoordinatesAt
  rw [readout_eq_retained N.n rs (gamma n*N.radius) S (endpointFrame Q N.frame 0) hs,
    readout_eq_retained N.n rt (gamma n*N.radius) T (endpointFrame Q N.frame (Fin.last (n+1))) ht]
  change pack ((2:ℝ) • retain N.n rs ((endpointFrame Q N.frame 0).toContinuousLinearMap.adjoint
      (compress (gamma n*N.radius) Y)))
      (retain N.n rt ((endpointFrame Q N.frame (Fin.last (n+1))).toContinuousLinearMap.adjoint
        (compress (gamma n*N.radius) Y)))=
    pack (retain N.n rs ((2:ℝ) • (endpointFrame Q N.frame 0).toContinuousLinearMap.adjoint
      (compress (gamma n*N.radius) Y)))
      (retain N.n rt ((endpointFrame Q N.frame (Fin.last (n+1))).toContinuousLinearMap.adjoint
        (compress (gamma n*N.radius) Y)))
  rw [map_smul]

theorem physicalPayload_eq_prefixAt {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (r s : ℕ) (hrs : r≤s) (hnext : r≤N.n → r<s) (S T : Fin (N.n+1) → Physical n D)
    (hs : ∀ k : Fin (N.n+1),k.val<s → S k=endpointFrame Q N.frame 0 (basis k))
    (ht : ∀ k : Fin (N.n+1),k.val<r → T k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))
    (hh : 0<N.width) (Y : Physical n D)
    (hb : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|≤3*N.width/16) :
    physicalPayload Q N Y=prefixPhysicalPayloadAt N s r S T Y := by
  unfold prefixPhysicalPayloadAt
  rw [prefixPhysicalCoordinatesAt_eq_retained Q N s r S T hs ht]
  exact ChiSplitChain.payload_flexible_prefix N.n r s hrs hnext N.ell N.width N.receiver N.nu N.force
    N.parentWidth N.tailRadius hh (physicalCoordinates Q N Y) hb

theorem physicalCentered_eq_prefixAt {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) (hℓ : P.ℓ=N.ell) (hβ : P.β=N.width)
    (r s : ℕ) (hrs : r≤s) (S T : Fin (N.n+1) → Physical n D)
    (hs : ∀ k : Fin (N.n+1),k.val<s → S k=endpointFrame Q N.frame 0 (basis k))
    (ht : ∀ k : Fin (N.n+1),k.val<r → T k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))
    (hh : 0<N.width) (Y : Physical n D)
    (hb : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|≤3*N.width/16) :
    physicalPayload Q N Y-physicalFineFrontier Q N P Y=
      prefixPhysicalPayloadAt N s r S T Y-ChiSplitFine.frontier N.n P.ℓ P.β (prefixPhysicalCoordinatesAt N s r S T Y) := by
  unfold prefixPhysicalPayloadAt physicalFineFrontier
  rw [Function.comp_apply,prefixPhysicalCoordinatesAt_eq_retained Q N s r S T hs ht,hℓ,hβ]
  exact ChiSplitChain.centeredPayload_flexible_prefix N.n r s hrs N.ell N.width N.receiver N.nu N.force
    N.parentWidth N.tailRadius hh (physicalCoordinates Q N Y) hb

theorem physicalFinePiece_eq_prefixAt {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) (p r s : ℕ) (hrs : r≤s) (hnext : r≤N.n → r<s)
    (S T : Fin (N.n+1) → Physical n D)
    (hs : ∀ k : Fin (N.n+1),k.val<s → S k=endpointFrame Q N.frame 0 (basis k))
    (ht : ∀ k : Fin (N.n+1),k.val<r → T k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))
    (Y : Physical n D)
    (hb : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|≤3*P.β/16) :
    physicalFinePiece Q N P p Y=ChiSplitFine.pieces P N.n p (prefixPhysicalCoordinatesAt N s r S T Y) := by
  rw [prefixPhysicalCoordinatesAt_eq_retained Q N s r S T hs ht]
  exact ChiSplitFine.pieces_flexible_prefix P N.n p r s hrs hnext (physicalCoordinates Q N Y) hb

theorem physicalRelease_eq_prefix {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (r : ℕ)
    (T : Fin (N.n+1) → Physical n D)
    (ht : ∀ k : Fin (N.n+1),k.val<r → T k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))
    (hhp : 0<N.parentWidth) (hw : N.width≤N.parentWidth) (Y : Physical n D)
    (hb : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|≤N.width/4) :
    physicalRelease Q N Y=prefixPhysicalRelease N r T Y :=
  actual_release_eq_virtual (targetNode Q N) r T ht hhp hw Y hb

theorem physicalNodeOrigin_eq {D : ℕ} (N : Node (Block D)) : N.H 0=physicalNodeOrigin N := by
  simp only [Node.H,Node.coordinates_zero,physicalNodeOrigin]

end Bilevel.EndpointTransportResponse
