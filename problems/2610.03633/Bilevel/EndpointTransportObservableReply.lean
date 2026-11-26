import Bilevel.EndpointTransportObservablePrefix
import Bilevel.EndpointTransportVirtualReply

/-! Literal physical nonlinear reply from observable ancestor and endpoint
arrays. No terminal ordinary latent frame columns are assumed available. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalHierarchy_observable_inverse_core_germ {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (hR : ∀ i : Fin J,0<R (i.val+1))
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D) (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (h : ObservablePhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns columns S T)
    (hmw : 0<M.width) (hmR : 0<M.radius) (κ : NNReal) (hκ : κ<1)
    (hH : ∀ z,‖iteratedFDeriv ℝ 2
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(κ:ℝ))
    (hF : LipschitzWith κ (gradient (physicalExtension (U:=Blocks J (Block D)) (D:=D)
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn))))
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16)
    (x : HybridOuter E (Blocks J (Block D)) D)
    (y : HybridVariables (Blocks J (Block D)) (Normals s) n D) (hy : y∈physicalNormalKnown W Z s)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates x.fst.fst a|≤M.width/8) :
    let z := jointSolution hF hκ x y
    physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn =ᶠ[
      𝓝 (pack (pack x.fst.fst z.fst) z.snd)]
      prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
        rM r sourceCount macroColumns columns S T := by
  have he := prefixPhysicalHierarchyExtension_congr_ordinary M G P coarseIndex radialIndex fineIndex ρ R dn
    rM r sourceCount macroColumns (completeOrdinaryColumns G J columns) columns S T
    (fun k A hk => completeOrdinaryColumns_below G J columns k A hk)
  have hh := physicalHierarchy_inverse_core_germ Q M G P coarseIndex radialIndex fineIndex ρ R dn hR
    W Z rM r sourceCount macroColumns (completeOrdinaryColumns G J columns) S T h.complete
    hmw hmR κ hκ hH hF δ hδ hδM hδG x y hy hmb
  simpa only [he] using hh

theorem physicalHierarchy_observable_inverse_reply_eq_prefix {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (hR : ∀ i : Fin J,0<R (i.val+1))
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D) (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (h : ObservablePhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns columns S T)
    (hmw : 0<M.width) (hmR : 0<M.radius) (κ : NNReal) (hκ : κ<1)
    (hH : ∀ z,‖iteratedFDeriv ℝ 2
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(κ:ℝ))
    (hF : LipschitzWith κ (gradient (physicalExtension (U:=Blocks J (Block D)) (D:=D)
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn))))
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16)
    (x : HybridOuter E (Blocks J (Block D)) D)
    (y : HybridVariables (Blocks J (Block D)) (Normals s) n D) (hy : y∈physicalNormalKnown W Z s)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates x.fst.fst a|≤M.width/8)
    (ε : NNReal) (hε : ε<1)
    (hG : LipschitzWith ε (gradient (physicalExtension (U:=Blocks J (Block D)) (D:=D)
      (prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
        rM r sourceCount macroColumns columns S T)))) :
    jointSolution hF hκ x y=jointSolution hG hε x y ∧
      jointGradient hF hκ (pack x y)=jointGradient hG hε (pack x y) := by
  apply physical_jointGradient_eq_of_core_germ hκ hε hF hG x y
  exact physicalHierarchy_observable_inverse_core_germ Q M G P coarseIndex radialIndex fineIndex ρ R dn hR
    W Z rM r sourceCount macroColumns columns S T h hmw hmR κ hκ hH hF δ hδ hδM hδG x y hy hmb

end Bilevel.EndpointTransportResponse
