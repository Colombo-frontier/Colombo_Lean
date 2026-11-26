import Bilevel.EndpointTransportVirtualNeighborhood

/-! Actual full physical scalar germ from reachable disclosed prefixes.
The identity holds on an open neighborhood in every variable, so it gives
full ambient gradient equality, not only restricted tangent equality. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalHierarchyExtension_eventuallyEq_prefix {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hm : ∀ a : Fin (M.n+1),a.val<rM → macroColumns a=M.frame (basis a))
    (hprefix : ∀ k A,∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a))
    (hmw : 0<M.width) (hh : ∀ k A,k≤J → 0<(G k A).width)
    (hhp : ∀ k A,k≤J → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤J → (G k A).width≤(G k A).parentWidth)
    (hℓ : ∀ A,P.ℓ=(G J A).ell) (hβ : ∀ A,P.β=(G J A).width)
    (hrs : ∀ A,r J A≤sourceCount J A)
    (hs : ∀ A,∀ a : Fin ((G J A).n+1),a.val<sourceCount J A → S J A a=endpointFrame Q (G J A).frame 0 (basis a))
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → T J A a=endpointFrame Q (G J A).frame (Fin.last (n+1)) (basis a))
    (hfuture : ∀ k,k<J → ∀ A,∀ i : Fin ((G k A).n+1),r k A ≤ i.val →
      r (k+1) (child A i.val)≤(G (k+1) (child A i.val)).n)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance G r sourceCount J 0 [i.val])
    (hmR : 0<M.radius) (hR : ∀ k A,k≤J → 0<(G k A).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16)
    (z : Full (PhysicalBase E J n D) s)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates z.fst.fst a|≤M.width/8)
    (hb : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block J k z.fst.snd.fst) a|≤(G k A).width/8)
    (hbt : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) z.fst.snd.snd).snd a|≤(G J A).width/8) :
    physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn =ᶠ[𝓝 z]
      prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
        rM r sourceCount macroColumns columns S T := by
  have hnear := physical_eventually_blind_uniform Q M G rM r hmR hR δ hδ hδM hδG z hmb hb hbt
  filter_upwards [hnear] with y hy
  exact physicalHierarchyExtension_eq_prefix Q M G P coarseIndex radialIndex fineIndex ρ R dn
    rM r sourceCount macroColumns columns S T hm hprefix hmw hh hhp hw hℓ hβ hrs hs ht hfuture hfront
    y hy.1 hy.2.1 hy.2.2

end Bilevel.EndpointTransportResponse
