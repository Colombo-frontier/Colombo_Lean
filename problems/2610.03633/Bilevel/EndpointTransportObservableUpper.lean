import Bilevel.EndpointTransportObservablePrefix
import Bilevel.EndpointTransportUpperProjection

/-! Literal physical nonlinear reply from observable ancestor and endpoint
arrays. No terminal ordinary latent frame columns are assumed available. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiTreeProgress ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalUpper_gradient_eq_observable_prefix {J n D s : ℕ} (Q : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (P : ChiFine.Parameters) (hJ : 0<J)
    (ρ R : ℝ) (b : Normals s)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D) (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (h : ObservablePhysicalPrefixCertificate Q M G P W Z rM r sourceCount macroColumns columns S T)
    (hmw : 0<M.width) (hmR : 0<M.radius)
    (hmfuture : ∀ i : Fin (M.n+1),rM ≤ i.val → r 0 [i.val]≤(G 0 [i.val]).n)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16)
    (x : HybridOuter E (Blocks J (Block D)) D)
    (y : HybridVariables (Blocks J (Block D)) (Normals s) n D) (hy : y∈physicalNormalKnown W Z s)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates x.fst.fst a|≤M.width/8) :
    gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D) (physicalUpperBase J Q M ν G J ρ R) b) (pack x y)=
    gradient (physicalUpper (U:=Blocks J (Block D)) (D:=D)
      (prefixPhysicalUpperBase J M ν G J ρ R rM r macroColumns columns T) b) (pack x y) := by
  have he := prefixPhysicalUpperBase_congr_ordinary (m:=J) M ν G J hJ ρ R rM r macroColumns
    (completeOrdinaryColumns G J columns) columns T
    (fun k A hk => completeOrdinaryColumns_below G J columns k A hk)
  have hh := physicalUpper_gradient_eq_prefix_of_projection Q M ν G P hJ ρ R b W Z rM r sourceCount
    macroColumns (completeOrdinaryColumns G J columns) S T h.complete hmw hmR hmfuture
    δ hδ hδM hδG x y hy hmb
  simpa only [he] using hh

end Bilevel.EndpointTransportResponse
