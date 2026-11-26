import Bilevel.EndpointTransportPrefixAssembly
import Bilevel.ChiSourceInverseGeometry

/-! Source scale geometry assembled before specializing the frame family.
All remaining hypotheses are literal known-column and projected-column
facts, not support or inverse conclusions. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration PrimitiveGeometry EndpointTransportMatrix
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem source_physical_prefix_geometry {J n D : ℕ} (Q : Rotations n D)
    (initial : Scale) (ratios resolutions weight : ℕ → ℝ) (A Kminus ζ cn CR : ℝ)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] Block D)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR)
    (P : ChiFine.Parameters) (W : Fin J → Submodule ℝ (Block D))
    (Z : Index n → Submodule ℝ (Block D)) (r : ℕ → List ℕ → ℕ) :
    let G := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V
    P.ℓ=(G J []).ell → P.β=(G J []).width →
    (∀ k I,∀ hk : k<J,∀ a : Fin ((G k I).n+1),a.val<r k I → (G k I).frame (basis a)∈W ⟨k,hk⟩) →
    (∀ k I,∀ hk : k<J,∀ a : Fin ((G k I).n+1),r k I≤a.val →
      (G k I).radius*‖(W ⟨k,hk⟩).orthogonalProjection ((G k I).frame (basis a))‖≤(G k I).width/8) →
    (∀ I,∀ a : Fin ((G J I).n+1),a.val<r J I → Q 0 ((G J I).frame (basis a))∈Z 0) →
    (∀ I,∀ a : Fin ((G J I).n+1),a.val<r J I → Q (Fin.last (n+1)) ((G J I).frame (basis a))∈Z (Fin.last (n+1))) →
    (∀ I,∀ a : Fin ((G J I).n+1),r J I≤a.val →
      (EndpointTransportMatrix.gamma n*(G J I).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((G J I).frame (basis a)))‖≤(G J I).width/8) →
    (∀ k,k<J → ∀ I,∀ i : Fin ((G k I).n+1),r k I ≤ i.val →
      r (k+1) (child I i.val)≤(G (k+1) (child I i.val)).n) →
    PhysicalPrefixGeometry Q G P W Z r := by
  dsimp only
  intro hℓ hβ hknown hmargin hs ht htp hf
  have hp := parentScale_positive initial ratios resolutions hl hw hr hη
  apply physicalPrefixGeometry_of_margins Q _ P W Z r
    (fun k _ _ => (hp (k+1)).2) _ (fun k _ _ => (hp k).2) _
    (fun _ => hℓ) (fun _ => hβ) hknown hmargin hs ht htp hf
  · intro k I _
    exact source_radial_radius_pos hCR (hp k).1 (hp k).2
      (zero_lt_one.trans_le (hr k)) (hweight k) hζ
  · intro k I _
    change resolutions k*(parentScale initial ratios resolutions k).width/ratios k≤
      (parentScale initial ratios resolutions k).width
    apply (div_le_iff₀ (zero_lt_one.trans_le (hr k))).mpr
    exact (mul_le_mul_of_nonneg_right ((hη1 k).trans (hr k)) (hp k).2.le).trans_eq (mul_comm _ _)

end Bilevel.EndpointTransportResponse
