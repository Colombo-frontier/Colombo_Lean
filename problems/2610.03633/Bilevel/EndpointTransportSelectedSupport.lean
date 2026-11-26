import Bilevel.EndpointTransportParentSupport
import Bilevel.EndpointTransportFineSelection
import Bilevel.ChiLiftedFrontierSupport

/-! Actual selected physical fine-piece support with only the reachable
source frontier disclosed. All target endpoint columns keep their old
prefix. Future ancestor selectors vanish at the actual blind point. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry PartialLegendre

theorem selectedPhysicalFinePiece_frontier_support {m n D : ℕ} (Q : Rotations n D)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (p d j : ℕ) (I : List ℕ) (hm : j+d≤m)
    (W : Fin m → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (x : HybridTangent (Blocks m (Block D)) n D) (r : ℕ → List ℕ → ℕ)
    (hancestor : ∀ k A,j≤k → ∀ hkd : k<j+d,BlindNode W x.fst ⟨k,by omega⟩ (G k A) (r k A))
    (hfront : FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) d j I)
    (hR : ∀ A,0<(G (j+d) A).radius)
    (hs : ∀ A,∀ k : Fin ((G (j+d) A).n+1),k.val<r (j+d) A →
      Q 0 ((G (j+d) A).frame (basis k))∈Z 0)
    (ht : ∀ A,∀ k : Fin ((G (j+d) A).n+1),k.val<r (j+d) A →
      Q (Fin.last (n+1)) ((G (j+d) A).frame (basis k))∈Z (Fin.last (n+1)))
    (hp : ∀ A,∀ k : Fin ((G (j+d) A).n+1),r (j+d) A≤k.val →
      (gamma n*(G (j+d) A).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((G (j+d) A).frame (basis k)))‖≤P.β/8)
    (hY : x.snd∈knownSpace Z) :
    gradient (selectedPhysicalFinePiece m G jointFstLinear jointSndLinear Q P p d j I) x∈physicalTangentKnown W Z := by
  apply ChiLiftedCarrier.selectFamily_gradient_mem_frontier G jointFstLinear _
    (fun k A => (physicalFinePiece_contDiff Q (G k A) P p).comp jointSndLinear.contDiff)
    d j I (Submodule.comap (Q 0).toLinearMap (Z 0)) (physicalTangentKnown W Z) x r hfront
  · intro k A hk hkd i
    exact fst_composition_gradient_mem (knownSpace W) (knownSpace Z)
      (jointSelector_contDiff m k (G k A) i 3) x ((hancestor k A hk hkd).selector_mem i)
  · intro k A hk hkd i hi
    exact (hancestor k A hk hkd).selector_future_zero i hi
  · intro A hA
    apply snd_composition_gradient_mem (knownSpace W) (knownSpace Z) (physicalFinePiece_contDiff Q (G (j+d) A) P p) x
    apply physical_fine_support_on_product Q (G (j+d) A) (hR A) P p (r (j+d) A) Z _ (ht A) (hp A) x.snd hY
    intro k hk
    by_cases hkr : k.val<r (j+d) A
    · exact hs A k hkr
    · exact hA k (by omega)

end Bilevel.EndpointTransportResponse
