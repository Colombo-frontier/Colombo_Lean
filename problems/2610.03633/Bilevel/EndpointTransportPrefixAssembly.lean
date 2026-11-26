import Bilevel.EndpointTransportObservablePrefix

/-! Opaque geometric assembly keeps source record reductions outside the
kernel's arithmetic proof terms. All premises are explicit column facts. -/
noncomputable section
set_option maxHeartbeats 500000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry PartialLegendre

theorem physicalPrefixGeometry_of_margins {J n D : ℕ} (Q : Rotations n D)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ)
    (hh : ∀ k A,k≤J → 0<(G k A).width) (hR : ∀ k A,k≤J → 0<(G k A).radius)
    (hp : ∀ k A,k≤J → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤J → (G k A).width≤(G k A).parentWidth)
    (hℓ : ∀ A,P.ℓ=(G J A).ell) (hβ : ∀ A,P.β=(G J A).width)
    (hknown : ∀ k A,∀ hk : k<J,∀ a : Fin ((G k A).n+1),a.val<r k A → (G k A).frame (basis a)∈W ⟨k,hk⟩)
    (hmargin : ∀ k A,∀ hk : k<J,∀ a : Fin ((G k A).n+1),r k A≤a.val →
      (G k A).radius*‖(W ⟨k,hk⟩).orthogonalProjection ((G k A).frame (basis a))‖≤(G k A).width/8)
    (hs : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → Q 0 ((G J A).frame (basis a))∈Z 0)
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → Q (Fin.last (n+1)) ((G J A).frame (basis a))∈Z (Fin.last (n+1)))
    (htp : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      (gamma n*(G J A).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((G J A).frame (basis a)))‖≤(G J A).width/8)
    (hf : ∀ k,k<J → ∀ A,∀ i : Fin ((G k A).n+1),r k A ≤ i.val →
      r (k+1) (child A i.val)≤(G (k+1) (child A i.val)).n) :
    PhysicalPrefixGeometry Q G P W Z r := by
  refine ⟨?_,fun A => hh J A le_rfl,fun A => hR J A le_rfl,hp,hw,hℓ,hβ,hs,ht,htp,hf⟩
  intro k A hk
  refine ⟨hh k A hk.le,hR k A hk.le,hknown k A hk,?_⟩
  intro a ha
  have h := hmargin k A hk a ha
  have hpos := hh k A hk.le
  linarith only [h,hpos]

end Bilevel.EndpointTransportResponse
