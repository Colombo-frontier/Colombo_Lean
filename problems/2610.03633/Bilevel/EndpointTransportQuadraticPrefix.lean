import Bilevel.EndpointTransportMacroGerm
import Bilevel.EndpointTransportPayloadPrefix

/-! Exact depth-zero physical upper evaluation from endpoint prefixes.
The source and target prefix lengths are explicitly different. These are
scalar/local-gradient identities; no adaptive disclosure bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiPrefixEvaluation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def prefixQuadraticCore {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ) (r : Fin (M.n+1) → ℕ)
    (macroColumns : Fin (M.n+1) → E)
    (sourceColumns targetColumns : ∀ i : Fin (M.n+1),Fin ((G 0 [i.val]).n+1) → Physical n D)
    (z : Joint E (Physical n D)) : ℝ :=
  prefixPhysicalMacro Q M ν (fun i => G 0 [i.val]) rM r macroColumns targetColumns z+
    (∑ i : Fin (M.n+1),virtualOuterSelector M rM macroColumns i z.fst*
      (prefixPhysicalPayload (G 0 [i.val]) (r i) (sourceColumns i) (targetColumns i) z.snd-
        payload (G 0 [i.val]).n (G 0 [i.val]).ell (G 0 [i.val]).width (G 0 [i.val]).receiver
          (G 0 [i.val]).nu (G 0 [i.val]).force (G 0 [i.val]).parentWidth (G 0 [i.val]).tailRadius 0))+
    RadialWrapper.bowl (ρ/EndpointTransportMatrix.gamma n^2) (EndpointTransportMatrix.gamma n*R) z.snd

theorem quadraticCore_eq_prefix {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (rM : ℕ) (r : Fin (M.n+1) → ℕ)
    (macroColumns : Fin (M.n+1) → E)
    (sourceColumns targetColumns : ∀ i : Fin (M.n+1),Fin ((G 0 [i.val]).n+1) → Physical n D)
    (hm : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hs : ∀ i,∀ k : Fin ((G 0 [i.val]).n+1),k.val<r i+1 →
      sourceColumns i k=endpointFrame Q (G 0 [i.val]).frame 0 (basis k))
    (ht : ∀ i,∀ k : Fin ((G 0 [i.val]).n+1),k.val<r i →
      targetColumns i k=endpointFrame Q (G 0 [i.val]).frame (Fin.last (n+1)) (basis k))
    (hmw : 0<M.width) (hh : ∀ i : Fin (M.n+1),0<(G 0 [i.val]).width)
    (hhp : ∀ i : Fin (M.n+1),0<(G 0 [i.val]).parentWidth)
    (hw : ∀ i : Fin (M.n+1),(G 0 [i.val]).width≤(G 0 [i.val]).parentWidth)
    (hfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r i≤(G 0 [i.val]).n)
    (z : Joint E (Physical n D))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ i,∀ k : Fin ((G 0 [i.val]).n+1),r i≤k.val →
      |(physicalCoordinates Q (G 0 [i.val]) z.snd).snd k|≤(G 0 [i.val]).width/4) :
    quadraticCore Q M ν G ρ R z=
      prefixQuadraticCore Q M ν G ρ R rM r macroColumns sourceColumns targetColumns z := by
  have hmval := physical_macro_release_eq_prefix Q M ν (fun i => G 0 [i.val]) rM r
    macroColumns targetColumns hm ht hmw hhp hw hfuture z hmBlind hblind
  have hc : outerPhysicalCarrier 0 Q M (jointFstLinear (A:=E) (B:=Physical n D)) G 0
      (jointSndLinear (A:=E) (B:=Physical n D)) 0 0 z=
      ∑ i : Fin (M.n+1),virtualOuterSelector M rM macroColumns i z.fst*
        (prefixPhysicalPayload (G 0 [i.val]) (r i) (sourceColumns i) (targetColumns i) z.snd-
          payload (G 0 [i.val]).n (G 0 [i.val]).ell (G 0 [i.val]).width (G 0 [i.val]).receiver
            (G 0 [i.val]).nu (G 0 [i.val]).force (G 0 [i.val]).parentWidth (G 0 [i.val]).tailRadius 0) := by
    unfold outerPhysicalCarrier macroSelected
    apply Finset.sum_congr rfl
    intro i _
    change wrappedSelector M i z.fst*(physicalPayload Q (G 0 [i.val]) z.snd-(G 0 [i.val]).H 0)=_
    rw [actual_outerSelector_eq_virtual M rM macroColumns hm hmw i z.fst hmBlind,
      physicalPayload_eq_prefix Q (G 0 [i.val]) (r i) (sourceColumns i) (targetColumns i)
        (hs i) (ht i) (hh i) z.snd (hblind i),Node.H,Node.coordinates_zero]
  unfold quadraticCore quadraticCoreLower prefixQuadraticCore
  linarith only [hmval,hc]

end Bilevel.EndpointTransportResponse
