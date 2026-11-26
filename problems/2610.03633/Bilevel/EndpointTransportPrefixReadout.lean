import Bilevel.EndpointTransportFineLeaves
import Bilevel.ChiSplitFinePiecePrefix
import Bilevel.ChiPrefixReadout

/-! Explicit physical endpoint-prefix readout. Source and predecessor
columns are separate, with retained sizes r+1 and r; the full physical
vector is compressed before either readout. No ordinary-frame substitution
or restriction to the response graph is made. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive PrimitiveGeometry RadialWrapper ChiPrefixEvaluation

def physicalPrefixCoordinates {n D : ℕ} (N : Node (Block D)) (r : ℕ)
    (sourceColumns targetColumns : Fin (N.n+1) → Physical n D) (Y : Physical n D) : ChiSplitChain.Latent N.n :=
  pack ((2:ℝ) • ChiPrefixEvaluation.readout N.n (r+1) (gamma n*N.radius) sourceColumns Y)
    (ChiPrefixEvaluation.readout N.n r (gamma n*N.radius) targetColumns Y)

theorem physicalPrefixCoordinates_eq_retained {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (r : ℕ)
    (sourceColumns targetColumns : Fin (N.n+1) → Physical n D)
    (hs : ∀ k : Fin (N.n+1),k.val<r+1 → sourceColumns k=endpointFrame Q N.frame 0 (basis k))
    (ht : ∀ k : Fin (N.n+1),k.val<r → targetColumns k=endpointFrame Q N.frame (Fin.last (n+1)) (basis k))
    (Y : Physical n D) :
    physicalPrefixCoordinates N r sourceColumns targetColumns Y=
      ChiSplitFine.retainSplit N.n r (physicalCoordinates Q N Y) := by
  unfold physicalPrefixCoordinates
  rw [readout_eq_retained N.n (r+1) (gamma n*N.radius) sourceColumns (endpointFrame Q N.frame 0) hs,
    readout_eq_retained N.n r (gamma n*N.radius) targetColumns (endpointFrame Q N.frame (Fin.last (n+1))) ht]
  change pack ((2:ℝ) • retain N.n (r+1) ((endpointFrame Q N.frame 0).toContinuousLinearMap.adjoint
      (compress (gamma n*N.radius) Y)))
      (retain N.n r ((endpointFrame Q N.frame (Fin.last (n+1))).toContinuousLinearMap.adjoint
        (compress (gamma n*N.radius) Y)))=
    pack (retain N.n (r+1) ((2:ℝ) • (endpointFrame Q N.frame 0).toContinuousLinearMap.adjoint
      (compress (gamma n*N.radius) Y)))
      (retain N.n r ((endpointFrame Q N.frame (Fin.last (n+1))).toContinuousLinearMap.adjoint
        (compress (gamma n*N.radius) Y)))
  rw [map_smul]

theorem physicalPrefixCoordinates_continuous {n D : ℕ} (N : Node (Block D)) (r : ℕ) :
    Continuous (fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D =>
      physicalPrefixCoordinates N r p.1.1 p.1.2 p.2) := by
  have hs : Continuous (fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D =>
      ChiPrefixEvaluation.readout N.n (r+1) (gamma n*N.radius) p.1.1 p.2) := Continuous.comp
      (g:=fun q : (Fin (N.n+1) → Physical n D) × Physical n D =>
        ChiPrefixEvaluation.readout N.n (r+1) (gamma n*N.radius) q.1 q.2)
      (f:=fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D => (p.1.1,p.2))
      (readout_continuous (E:=Physical n D) N.n (r+1) (gamma n*N.radius))
      (continuous_fst.fst.prodMk continuous_snd)
  have ht : Continuous (fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D =>
      ChiPrefixEvaluation.readout N.n r (gamma n*N.radius) p.1.2 p.2) := Continuous.comp
      (g:=fun q : (Fin (N.n+1) → Physical n D) × Physical n D =>
        ChiPrefixEvaluation.readout N.n r (gamma n*N.radius) q.1 q.2)
      (f:=fun p : ((Fin (N.n+1) → Physical n D) × (Fin (N.n+1) → Physical n D)) × Physical n D => (p.1.2,p.2))
      (readout_continuous (E:=Physical n D) N.n r (gamma n*N.radius))
      (continuous_fst.snd.prodMk continuous_snd)
  exact (packLinear (X:=Space N.n) (Y:=Space N.n)).continuous.comp ((hs.const_smul (2:ℝ)).prodMk ht)

end Bilevel.EndpointTransportResponse
