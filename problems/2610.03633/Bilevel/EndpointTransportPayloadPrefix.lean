import Bilevel.EndpointTransportPrefixReadout
import Bilevel.ChiSplitPayloadPrefix

/-! Full physical payload evaluation, including both terminal receivers,
from separate endpoint prefixes. The actual physical compression is kept. -/
noncomputable section
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive PrimitiveGeometry ChiPrefixEvaluation

variable {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (r : ℕ)
  (sourceColumns targetColumns : Fin (N.n+1) → Physical n D)
  (hs : ∀ k : Fin (N.n+1),k.val<r+1 → sourceColumns k=endpointFrame Q N.frame 0 (basis k))
  (ht : ∀ k : Fin (N.n+1),k.val<r → targetColumns k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))

def prefixPhysicalPayload : Physical n D → ℝ :=
  ChiSplitChain.payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius ∘
    physicalPrefixCoordinates N r sourceColumns targetColumns

include hs ht in
theorem physicalPayload_eq_prefix (hh : 0<N.width) (Y : Physical n D)
    (hblind : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|≤N.width/4) :
    physicalPayload Q N Y=prefixPhysicalPayload N r sourceColumns targetColumns Y := by
  unfold prefixPhysicalPayload
  rw [Function.comp_apply,physicalPrefixCoordinates_eq_retained Q N r sourceColumns targetColumns hs ht]
  exact ChiSplitChain.payload_prefix_value N.n r N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    hh (physicalCoordinates Q N Y) hblind

include hs ht in
theorem physicalPayload_eventuallyEq_prefix (hh : 0<N.width) (Y : Physical n D)
    (hblind : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|<N.width/4) :
    physicalPayload Q N =ᶠ[𝓝 Y] prefixPhysicalPayload N r sourceColumns targetColumns := by
  have hlatent := ChiSplitChain.payload_prefix_eventually N.n r N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    hh (physicalCoordinates Q N Y) hblind
  have hlocal := hlatent.comp_tendsto (physicalCoordinates_contDiff Q N).continuous.continuousAt
  filter_upwards [hlocal] with y hy
  change ChiSplitChain.payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    (physicalCoordinates Q N y)=_
  unfold prefixPhysicalPayload
  rw [Function.comp_apply,physicalPrefixCoordinates_eq_retained Q N r sourceColumns targetColumns hs ht]
  exact hy

include hs ht in
theorem physicalPayload_gradient_eq_prefix (hh : 0<N.width) (Y : Physical n D)
    (hblind : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|<N.width/4) :
    gradient (physicalPayload Q N) Y=gradient (prefixPhysicalPayload N r sourceColumns targetColumns) Y :=
  (physicalPayload_eventuallyEq_prefix Q N r sourceColumns targetColumns hs ht hh Y hblind).gradient_eq

end Bilevel.EndpointTransportResponse
