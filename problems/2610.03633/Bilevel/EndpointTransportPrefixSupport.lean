import Bilevel.EndpointTransportPayloadPrefix
import Bilevel.EndpointTransportFinePrefix
import Bilevel.ChiSplitPrefixGradient
import Bilevel.ChiCarrierSupportSpace

/-! Actual full physical gradients lie in the queried physical direction
plus the disclosed source/target columns. The two endpoint prefixes remain
asymmetric, and radial derivative terms are retained. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive PrimitiveGeometry RadialWrapper ChiCarrier

theorem sourceReadout_adjoint {n D r : ℕ} (Q : Rotations n D) (U : Space r →ₗᵢ[ℝ] Block D) (z : Space r) :
    (sourceReadout Q U).adjoint z=(2:ℝ) • endpointFrame Q U 0 z := by
  simp only [sourceReadout,map_smul,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.smul_apply,LinearIsometry.coe_toContinuousLinearMap]

theorem targetReadout_adjoint {n D r : ℕ} (Q : Rotations n D) (U : Space r →ₗᵢ[ℝ] Block D) (z : Space r) :
    (targetReadout Q U).adjoint z=endpointFrame Q U (Fin.last (n+1)) z := by
  rw [targetReadout,ContinuousLinearMap.adjoint_adjoint]
  rfl

theorem physical_pullback_gradient_mem {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (hR : 0<N.radius)
    (f : ChiSplitChain.Latent N.n → ℝ) (hf : Differentiable ℝ f) (r : ℕ)
    (W : Submodule ℝ (Physical n D)) (Y : Physical n D) (hY : Y∈W)
    (hs : ∀ k : Fin (N.n+1),k.val<r+1 → endpointFrame Q N.frame 0 (basis k)∈W)
    (ht : ∀ k : Fin (N.n+1),k.val<r → endpointFrame Q N.frame (Fin.last (n+1)) (basis k)∈W)
    (hgs : ∀ k : Fin (N.n+1),r+1≤k.val → (gradient f (physicalCoordinates Q N Y)).fst k=0)
    (hgt : ∀ k : Fin (N.n+1),r≤k.val → (gradient f (physicalCoordinates Q N Y)).snd k=0) :
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

theorem physical_payload_gradient_mem {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hh : 0<N.width) (hR : 0<N.radius) (r : ℕ) (W : Submodule ℝ (Physical n D))
    (Y : Physical n D) (hY : Y∈W)
    (hs : ∀ k : Fin (N.n+1),k.val<r+1 → endpointFrame Q N.frame 0 (basis k)∈W)
    (ht : ∀ k : Fin (N.n+1),k.val<r → endpointFrame Q N.frame (Fin.last (n+1)) (basis k)∈W)
    (hb : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|<N.width/4) :
    gradient (physicalPayload Q N) Y∈W := by
  have hz := ChiSplitFine.payload_gradient_support N.n r N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    hh (physicalCoordinates Q N Y) hb
  exact physical_pullback_gradient_mem Q N hR _
    ((ChiSplitChain.payload_contDiff N.n 3 N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius).differentiable (by norm_num))
    r W Y hY hs ht hz.1 hz.2

theorem physical_fine_piece_gradient_mem {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hR : 0<N.radius) (P : ChiFine.Parameters) (j r : ℕ) (W : Submodule ℝ (Physical n D))
    (Y : Physical n D) (hY : Y∈W)
    (hs : ∀ k : Fin (N.n+1),k.val<r+1 → endpointFrame Q N.frame 0 (basis k)∈W)
    (ht : ∀ k : Fin (N.n+1),k.val<r → endpointFrame Q N.frame (Fin.last (n+1)) (basis k)∈W)
    (hb : ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|<P.β/4) :
    gradient (physicalFinePiece Q N P j) Y∈W := by
  have hz := ChiSplitFine.pieces_gradient_support P N.n j r (physicalCoordinates Q N Y) hb
  exact physical_pullback_gradient_mem Q N hR _ ((ChiSplitFine.pieces_contDiff P N.n j).differentiable (by norm_num))
    r W Y hY hs ht hz.1 hz.2

end Bilevel.EndpointTransportResponse
