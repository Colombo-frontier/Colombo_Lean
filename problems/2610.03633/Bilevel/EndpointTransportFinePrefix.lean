import Bilevel.EndpointTransportPrefixReadout

/-! Exact actual physical fine evaluation and full physical gradients from
separate disclosed endpoint prefixes. Blindness concerns only the target
endpoint; no source-coordinate smallness or response-graph identity is used. -/
noncomputable section
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive PrimitiveGeometry ChiPrefixEvaluation

variable {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (r : ℕ)
  (sourceColumns targetColumns : Fin (N.n+1) → Physical n D)
  (hs : ∀ k : Fin (N.n+1),k.val<r+1 → sourceColumns k=endpointFrame Q N.frame 0 (basis k))
  (ht : ∀ k : Fin (N.n+1),k.val<r → targetColumns k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))

include hs ht in
theorem physicalFinePiece_eq_prefix (P : ChiFine.Parameters) (j : ℕ) (Y : Physical n D)
    (hblind : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|≤P.β/4) :
    physicalFinePiece Q N P j Y=
      ChiSplitFine.pieces P N.n j (physicalPrefixCoordinates N r sourceColumns targetColumns Y) := by
  rw [physicalPrefixCoordinates_eq_retained Q N r sourceColumns targetColumns hs ht]
  exact ChiSplitFine.pieces_prefix_value P N.n j r (physicalCoordinates Q N Y) hblind

include hs ht in
theorem physicalFinePiece_eventuallyEq_prefix (P : ChiFine.Parameters) (j : ℕ) (Y : Physical n D)
    (hblind : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|<P.β/4) :
    physicalFinePiece Q N P j =ᶠ[𝓝 Y]
      (fun y => ChiSplitFine.pieces P N.n j (physicalPrefixCoordinates N r sourceColumns targetColumns y)) := by
  have hlatent := ChiSplitFine.value_prefix_eventually (ChiSplitFine.pieces P N.n j) r (P.β/4)
    (ChiSplitFine.pieces_prefix_value P N.n j r) (physicalCoordinates Q N Y) hblind
  have hlocal := hlatent.comp_tendsto (physicalCoordinates_contDiff Q N).continuous.continuousAt
  filter_upwards [hlocal] with y hy
  change ChiSplitFine.pieces P N.n j (physicalCoordinates Q N y)=_
  rw [physicalPrefixCoordinates_eq_retained Q N r sourceColumns targetColumns hs ht]
  exact hy

include hs ht in
theorem physicalFinePiece_gradient_eq_prefix (P : ChiFine.Parameters) (j : ℕ) (Y : Physical n D)
    (hblind : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|<P.β/4) :
    gradient (physicalFinePiece Q N P j) Y=
      gradient (fun y => ChiSplitFine.pieces P N.n j (physicalPrefixCoordinates N r sourceColumns targetColumns y)) Y :=
  (physicalFinePiece_eventuallyEq_prefix Q N r sourceColumns targetColumns hs ht P j Y hblind).gradient_eq

end Bilevel.EndpointTransportResponse
