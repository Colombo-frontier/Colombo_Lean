import Bilevel.EndpointTransportProductSupport
import Bilevel.EndpointTransportRelease
import Bilevel.ChiCarrierReleaseLocality

/-! The actual physical terminal release is supported in the old target
endpoint prefix. This includes its radial derivative on the entire physical
product known space; no response-graph identity is used. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier

theorem physical_release_flat_on_product {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hh : 0<N.width) (hR : 0<N.radius) (hhp : 0<N.parentWidth) (hw : N.width≤N.parentWidth)
    (r : ℕ) (hr : r≤N.n) (W : Index n → Submodule ℝ (Block D))
    [CompleteSpace (W (Fin.last (n+1)))]
    (hp : ∀ k : Fin (N.n+1),r≤k.val →
      (gamma n*N.radius)*‖(W (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) (N.frame (basis k)))‖≤N.width/8)
    (Y : Physical n D) (hY : Y∈knownSpace W) :
    physicalRelease Q N Y=0 ∧ fderiv ℝ (physicalRelease Q N) Y=0 := by
  have hb := physical_target_blind Q N hR (W (Fin.last (n+1))) r (N.width/8) hp Y (hY _)
    (Fin.last N.n) (by simpa using hr)
  apply (targetNode Q N).release_flat_of_blind_terminal hhp hw Y
  change |(physicalCoordinates Q N Y).snd (Fin.last N.n)|≤N.width/4
  linarith

theorem physical_release_gradient_zero_on_product {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hh : 0<N.width) (hR : 0<N.radius) (hhp : 0<N.parentWidth) (hw : N.width≤N.parentWidth)
    (r : ℕ) (hr : r≤N.n) (W : Index n → Submodule ℝ (Block D))
    [CompleteSpace (W (Fin.last (n+1)))]
    (hp : ∀ k : Fin (N.n+1),r≤k.val →
      (gamma n*N.radius)*‖(W (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) (N.frame (basis k)))‖≤N.width/8)
    (Y : Physical n D) (hY : Y∈knownSpace W) : gradient (physicalRelease Q N) Y=0 := by
  apply norm_eq_zero.mp
  rw [GradientJetBounds.gradient_norm_eq,
    (physical_release_flat_on_product Q N hh hR hhp hw r hr W hp Y hY).2,norm_zero]

theorem physical_release_support_on_product {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hh : 0<N.width) (hR : 0<N.radius) (hhp : 0<N.parentWidth) (hw : N.width≤N.parentWidth)
    (r : ℕ) (W : Index n → Submodule ℝ (Block D))
    [CompleteSpace (W (Fin.last (n+1)))]
    (ht : ∀ k : Fin (N.n+1),k.val<r →
      Q (Fin.last (n+1)) (N.frame (basis k))∈W (Fin.last (n+1)))
    (hp : ∀ k : Fin (N.n+1),r≤k.val →
      (gamma n*N.radius)*‖(W (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) (N.frame (basis k)))‖≤N.width/8)
    (Y : Physical n D) (hY : Y∈knownSpace W) :
    gradient (physicalRelease Q N) Y∈knownSpace W := by
  apply (targetNode Q N).release_gradient_mem r (mul_pos (lt_of_lt_of_le (by norm_num) (gamma_range n).1) hR) hhp hw Y (knownSpace W) hY
    (fun k hk => endpointFrame_mem_knownSpace Q N.frame W (Fin.last (n+1)) (basis k) (ht k hk))
  intro k hk
  have hb := physical_target_blind Q N hR (W (Fin.last (n+1))) r (N.width/8) hp Y (hY _) k hk
  change |(physicalCoordinates Q N Y).snd k|≤N.width/4
  linarith

end Bilevel.EndpointTransportResponse
