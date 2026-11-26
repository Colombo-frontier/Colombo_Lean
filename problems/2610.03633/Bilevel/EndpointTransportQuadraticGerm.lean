import Bilevel.EndpointTransportQuadraticPrefix
import Bilevel.EndpointTransportQuadraticTrace

/-! Full arbitrary-query upper-gradient equality for the actual quadratic
physical family, obtained from a common open scalar prefix germ. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiPrefixEvaluation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadraticCore_eventuallyEq_prefix {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
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
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤3*M.width/16)
    (hblind : ∀ i,∀ k : Fin ((G 0 [i.val]).n+1),r i≤k.val →
      |(physicalCoordinates Q (G 0 [i.val]) z.snd).snd k|≤3*(G 0 [i.val]).width/16)
    (hmR : 0<M.radius) (hR : ∀ i : Fin (M.n+1),0<(G 0 [i.val]).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16)
    (hδN : ∀ i : Fin (M.n+1),δ≤(G 0 [i.val]).width/16) :
    quadraticCore Q M ν G ρ R =ᶠ[𝓝 z]
      prefixQuadraticCore Q M ν G ρ R rM r macroColumns sourceColumns targetColumns := by
  have hmLocal := eventually_blind_uniform (fun _ : Unit => M) (fun _ => hmR)
    (fun _ => jointFstLinear (A:=E) (B:=Physical n D))
    (fun _ => ChiPrimitive.jointFstLinear_norm)
    (fun _ => rM) (fun _ => M.width/4) δ hδ z (by
      intro _ k hk
      change |M.coordinates z.fst k|≤M.width/4-δ
      have hb := hmBlind k hk
      linarith)
  have hnLocal := eventually_blind_uniform (fun i : Fin (M.n+1) => targetNode Q (G 0 [i.val]))
    (fun i => mul_pos (gamma_positive n) (hR i))
    (fun _ => jointSndLinear (A:=E) (B:=Physical n D))
    (fun _ => ChiPrimitive.jointSndLinear_norm)
    r (fun i => (G 0 [i.val]).width/4) δ hδ z (by
      intro i k hk
      change |(physicalCoordinates Q (G 0 [i.val]) z.snd).snd k|≤(G 0 [i.val]).width/4-δ
      have hb := hblind i k hk
      have hd := hδN i
      linarith)
  filter_upwards [hmLocal,hnLocal] with y hym hyn
  exact quadraticCore_eq_prefix Q M ν G ρ R rM r macroColumns sourceColumns targetColumns
    hm hs ht hmw hh hhp hw hfuture y (hym ()) hyn

theorem quadraticFullCore_gradient_eq_of_germ {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (f : Joint E (Physical n D) → ℝ)
    (z : Joint (Joint E (Block D)) (Physical n D))
    (he : quadraticCore Q M ν G ρ R =ᶠ[𝓝 (quadraticUpperProjection n D z)] f) :
    gradient (quadraticFullCore Q M ν G ρ R) z=
      gradient (f ∘ quadraticUpperProjection n D) z :=
  (he.comp_tendsto (quadraticUpperProjection (E:=E) n D).continuous.continuousAt).gradient_eq

end Bilevel.EndpointTransportResponse
