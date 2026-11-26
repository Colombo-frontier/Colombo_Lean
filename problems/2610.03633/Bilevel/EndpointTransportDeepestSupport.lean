import Bilevel.EndpointTransportCenteredSupport
import Bilevel.EndpointTransportNormalKnown
import Bilevel.EndpointTransportCoarseCarriers
import Bilevel.ChiLiftedSupportAlgebra

/-! The actual deepest physical coarse carrier uses only the old source and
target prefixes. The centered subtraction occurs before ancestor selection. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry PartialLegendre

theorem physical_deepest_eq_selected {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) :
    physicalCoarseCarrier m Q G jointFstLinear jointSndLinear P d j I d=
    ChiLiftedCarrier.selectFamily m G jointFstLinear
      (fun k A (x : HybridTangent (Blocks m (Block D)) n D) =>
        (physicalPayload Q (G k A) x.snd-physicalFineFrontier Q (G k A) P x.snd)-(G k A).H 0) d j I := by
  have hc := physicalCarrier_selectFamily m Q G
    (jointFstLinear : HybridTangent (Blocks m (Block D)) n D →L[ℝ] Blocks m (Block D)) jointSndLinear 0 d j I
  simp only [zero_add] at hc
  funext x
  rw [physicalCoarseCarrier,if_pos rfl,hc]
  change ChiLiftedCarrier.selectFamily m G jointFstLinear _ d j I x-
    ChiLiftedCarrier.selectFamily m G jointFstLinear _ d j I x=_
  rw [← ChiLiftedCarrier.selectFamily_sub]
  apply congrArg (fun f => ChiLiftedCarrier.selectFamily m G jointFstLinear f d j I x)
  funext k A y
  dsimp only [physicalCarrier,Function.comp_apply]
  change physicalPayload Q (G k A) y.snd-(G k A).H 0-physicalFineFrontier Q (G k A) P y.snd=
    (physicalPayload Q (G k A) y.snd-physicalFineFrontier Q (G k A) P y.snd)-(G k A).H 0
  ring

theorem physical_deepest_support {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (hm : j+d≤m)
    (W : Fin m → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (x : HybridTangent (Blocks m (Block D)) n D) (r : ℕ → List ℕ → ℕ)
    (hancestor : ∀ k A,j≤k → ∀ hkd : k<j+d,BlindNode W x.fst ⟨k,by omega⟩ (G k A) (r k A))
    (hh : ∀ A,0<(G (j+d) A).width) (hR : ∀ A,0<(G (j+d) A).radius)
    (hℓ : ∀ A,P.ℓ=(G (j+d) A).ell) (hβ : ∀ A,P.β=(G (j+d) A).width)
    (hs : ∀ A,∀ k : Fin ((G (j+d) A).n+1),k.val<r (j+d) A →
      Q 0 ((G (j+d) A).frame (basis k))∈Z 0)
    (ht : ∀ A,∀ k : Fin ((G (j+d) A).n+1),k.val<r (j+d) A →
      Q (Fin.last (n+1)) ((G (j+d) A).frame (basis k))∈Z (Fin.last (n+1)))
    (hp : ∀ A,∀ k : Fin ((G (j+d) A).n+1),r (j+d) A≤k.val →
      (gamma n*(G (j+d) A).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((G (j+d) A).frame (basis k)))‖≤(G (j+d) A).width/8)
    (hY : x.snd∈knownSpace Z) :
    gradient (physicalCoarseCarrier m Q G jointFstLinear jointSndLinear P d j I d) x∈physicalTangentKnown W Z := by
  rw [physical_deepest_eq_selected]
  apply ChiLiftedCarrier.selectFamily_gradient_mem G jointFstLinear
    (fun k A (y : HybridTangent (Blocks m (Block D)) n D) =>
      (physicalPayload Q (G k A) y.snd-physicalFineFrontier Q (G k A) P y.snd)-(G k A).H 0)
    (fun k A => (((physical_payload_contDiff Q (G k A) 3).sub
      (physicalFineFrontier_contDiff Q (G k A) P)).comp (jointSndLinear : HybridTangent (Blocks m (Block D)) n D →L[ℝ] Physical n D).contDiff).sub contDiff_const)
    d j I (physicalTangentKnown W Z) x
  · intro k A hk hkd i
    exact fst_composition_gradient_mem (knownSpace W) (knownSpace Z)
      (jointSelector_contDiff m k (G k A) i 3) x ((hancestor k A hk hkd).selector_mem i)
  · intro A
    have hb := physical_centered_support_on_product Q (G (j+d) A) (hh A) (hR A) P (hℓ A) (hβ A)
      (r (j+d) A) Z (hs A) (ht A) (hp A) x.snd hY
    have hsnd := snd_composition_gradient_mem (knownSpace W) (knownSpace Z)
      ((physical_payload_contDiff Q (G (j+d) A) 3).sub (physicalFineFrontier_contDiff Q (G (j+d) A) P)) x hb
    exact gradient_sub_const_mem (physicalTangentKnown W Z)
      (((physical_payload_contDiff Q (G (j+d) A) 3).sub
        (physicalFineFrontier_contDiff Q (G (j+d) A) P)).comp (jointSndLinear : HybridTangent (Blocks m (Block D)) n D →L[ℝ] Physical n D).contDiff) x ((G (j+d) A).H 0) hsnd

end Bilevel.EndpointTransportResponse
