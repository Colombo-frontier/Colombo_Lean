import Bilevel.ChiSplitCenteredPayload
import Bilevel.EndpointTransportProductSupport

/-! Exact old-prefix support for the physical deepest coarse leaf. The
source frontier is subtracted before differentiating, and the full-vector
radial derivative remains in the queried physical product known space. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive PrimitiveGeometry RadialWrapper ChiCarrier

theorem physical_pullback_two_prefix_gradient_mem {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hR : 0<N.radius) (f : ChiSplitChain.Latent N.n → ℝ) (hf : Differentiable ℝ f) (rs rt : ℕ)
    (W : Submodule ℝ (Physical n D)) (Y : Physical n D) (hY : Y∈W)
    (hs : ∀ k : Fin (N.n+1),k.val<rs → endpointFrame Q N.frame 0 (basis k)∈W)
    (ht : ∀ k : Fin (N.n+1),k.val<rt → endpointFrame Q N.frame (Fin.last (n+1)) (basis k)∈W)
    (hgs : ∀ k : Fin (N.n+1),rs≤k.val → (gradient f (physicalCoordinates Q N Y)).fst k=0)
    (hgt : ∀ k : Fin (N.n+1),rt≤k.val → (gradient f (physicalCoordinates Q N Y)).snd k=0) :
    gradient (f ∘ physicalCoordinates Q N) Y∈W := by
  let A := ChiSplitChain.readout (sourceReadout Q N.frame) (targetReadout Q N.frame)
  have hforce : A.adjoint (gradient f (physicalCoordinates Q N Y))∈W := by
    rw [ChiSplitChain.readout_adjoint,sourceReadout_adjoint,targetReadout_adjoint]
    exact W.add_mem
      (W.smul_mem _ (WrappedPrefixLocality.frame_mem_of_support (endpointFrame Q N.frame 0) W hs _ hgs))
      (WrappedPrefixLocality.frame_mem_of_support (endpointFrame Q N.frame (Fin.last (n+1))) W ht _ hgt)
  have h := wrapped_hasGradientAt 0 (gamma n*N.radius) (mul_pos (gamma_positive n) hR) f A Y
    (gradient f (physicalCoordinates Q N Y)) (hf _).hasGradientAt
  have he : wrapped 0 (gamma n*N.radius) f A=f ∘ physicalCoordinates Q N := by
    funext y
    simp only [wrapped,bowl,zero_mul,zero_div,zero_add,add_zero,Function.comp_apply]
    rfl
  rw [he] at h
  rw [h.gradient]
  exact W.add_mem (W.smul_mem _ hforce) (W.smul_mem _ hY)

theorem physical_centered_support_on_product {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hh : 0<N.width) (hR : 0<N.radius) (P : ChiFine.Parameters) (hℓ : P.ℓ=N.ell) (hβ : P.β=N.width)
    (r : ℕ) (W : Index n → Submodule ℝ (Block D))
    [CompleteSpace (W (Fin.last (n+1)))]
    (hs : ∀ k : Fin (N.n+1),k.val<r → Q 0 (N.frame (basis k))∈W 0)
    (ht : ∀ k : Fin (N.n+1),k.val<r → Q (Fin.last (n+1)) (N.frame (basis k))∈W (Fin.last (n+1)))
    (hp : ∀ k : Fin (N.n+1),r≤k.val →
      (gamma n*N.radius)*‖(W (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) (N.frame (basis k)))‖≤N.width/8)
    (Y : Physical n D) (hY : Y∈knownSpace W) :
    gradient (fun Z => physicalPayload Q N Z-physicalFineFrontier Q N P Z) Y∈knownSpace W := by
  have he : (fun Z => physicalPayload Q N Z-physicalFineFrontier Q N P Z)=
      ChiSplitChain.centeredPayload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius ∘
        physicalCoordinates Q N := by
    funext Z
    simp only [physicalPayload,physicalFineFrontier,Function.comp_apply,ChiSplitChain.centeredPayload,hℓ,hβ]
  rw [he]
  have hb := ChiSplitChain.centeredPayload_gradient_support N.n r N.ell N.width N.receiver N.nu N.force
    N.parentWidth N.tailRadius hh (physicalCoordinates Q N Y) (by
      intro k hk
      have h := physical_target_blind Q N hR (W (Fin.last (n+1))) r (N.width/8) hp Y (hY _) k hk
      linarith)
  exact physical_pullback_two_prefix_gradient_mem Q N hR _
    ((ChiSplitChain.centeredPayload_contDiff N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius).differentiable
      (by norm_num)) r r (knownSpace W) Y hY
    (fun k hk => endpointFrame_mem_knownSpace Q N.frame W 0 (basis k) (hs k hk))
    (fun k hk => endpointFrame_mem_knownSpace Q N.frame W (Fin.last (n+1)) (basis k) (ht k hk)) hb.1 hb.2

end Bilevel.EndpointTransportResponse
