import Bilevel.EndpointTransportQuadraticReachable
import Bilevel.EndpointTransportPrefixBorel

/-! Complete arrays represent the original full scalar globally. This
identity is only a Borel-family representation, not an algorithmic disclosure. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadraticCore_full_prefix {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (data : QuadraticPrefixData M G n)
    (hm : ∀ k,data.1 k=M.frame (basis k))
    (hs : ∀ i k,data.2.1 i k=endpointFrame Q (G 0 [i.val]).frame 0 (basis k))
    (ht : ∀ i k,data.2.2 i k=endpointFrame Q (G 0 [i.val]).frame (Fin.last (n+1)) (basis k))
    (hmw : 0<M.width) (hh : ∀ i : Fin (M.n+1),0<(G 0 [i.val]).width)
    (hhp : ∀ i : Fin (M.n+1),0<(G 0 [i.val]).parentWidth)
    (hw : ∀ i : Fin (M.n+1),(G 0 [i.val]).width≤(G 0 [i.val]).parentWidth) :
    quadraticCore Q M ν G ρ R=
      prefixQuadraticCore Q M ν G ρ R (M.n+1) (fun i => (G 0 [i.val]).n+1)
        data.1 data.2.1 data.2.2 := by
  funext z
  apply quadraticCore_eq_prefix_reachable Q M ν G ρ R (M.n+1)
    (fun i => (G 0 [i.val]).n+1) data.1 data.2.1 data.2.2
    (fun k _ => hm k) (fun i _ k _ => hs i k) (fun i k _ => ht i k) hmw hh hhp hw
  · intro i hi
    omega
  · intro k hk
    omega
  · intro i k hk
    omega

end Bilevel.EndpointTransportResponse
