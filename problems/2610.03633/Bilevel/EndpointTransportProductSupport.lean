import Bilevel.EndpointTransportPrefixSupport
import Bilevel.EndpointTransportTargetProjection

/-! Concrete layerwise projection bounds imply full physical leaf support
at every point of the product known space. A new source endpoint column is
admitted while the target endpoint retains only its old prefix. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier

theorem endpointFrame_mem_knownSpace {n D q : ℕ} (Q : Rotations n D) (U : Space q →ₗᵢ[ℝ] Block D)
    (W : Index n → Submodule ℝ (Block D)) (j : Index n) (v : Space q) (hv : Q j (U v)∈W j) :
    endpointFrame Q U j v∈knownSpace W := by
  intro i
  change insertion (n+2) j (Q j (U v)) i∈W i
  rw [insertion_apply]
  by_cases hi : i=j
  · subst i
    simpa only [if_pos rfl,if_true] using hv
  · rw [if_neg hi]
    exact (W i).zero_mem

theorem physical_payload_support_on_product {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hh : 0<N.width) (hR : 0<N.radius) (r : ℕ)
    (W : Index n → Submodule ℝ (Block D)) [CompleteSpace (W (Fin.last (n+1)))]
    (hs : ∀ k : Fin (N.n+1),k.val<r+1 → Q 0 (N.frame (basis k))∈W 0)
    (ht : ∀ k : Fin (N.n+1),k.val<r → Q (Fin.last (n+1)) (N.frame (basis k))∈W (Fin.last (n+1)))
    (hp : ∀ k : Fin (N.n+1),r≤k.val →
      (gamma n*N.radius)*‖(W (Fin.last (n+1))).orthogonalProjection (Q (Fin.last (n+1)) (N.frame (basis k)))‖≤N.width/8)
    (Y : Physical n D) (hY : Y∈knownSpace W) : gradient (physicalPayload Q N) Y∈knownSpace W := by
  apply physical_payload_gradient_mem Q N hh hR r (knownSpace W) Y hY
    (fun k hk => endpointFrame_mem_knownSpace Q N.frame W 0 (basis k) (hs k hk))
    (fun k hk => endpointFrame_mem_knownSpace Q N.frame W (Fin.last (n+1)) (basis k) (ht k hk))
  intro k hk
  have hb := physical_target_blind Q N hR (W (Fin.last (n+1))) r (N.width/8) hp Y (hY _) k hk
  linarith

theorem physical_fine_support_on_product {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hR : 0<N.radius) (P : ChiFine.Parameters) (j r : ℕ)
    (W : Index n → Submodule ℝ (Block D)) [CompleteSpace (W (Fin.last (n+1)))]
    (hs : ∀ k : Fin (N.n+1),k.val<r+1 → Q 0 (N.frame (basis k))∈W 0)
    (ht : ∀ k : Fin (N.n+1),k.val<r → Q (Fin.last (n+1)) (N.frame (basis k))∈W (Fin.last (n+1)))
    (hp : ∀ k : Fin (N.n+1),r≤k.val →
      (gamma n*N.radius)*‖(W (Fin.last (n+1))).orthogonalProjection (Q (Fin.last (n+1)) (N.frame (basis k)))‖≤P.β/8)
    (Y : Physical n D) (hY : Y∈knownSpace W) : gradient (physicalFinePiece Q N P j) Y∈knownSpace W := by
  apply physical_fine_piece_gradient_mem Q N hR P j r (knownSpace W) Y hY
    (fun k hk => endpointFrame_mem_knownSpace Q N.frame W 0 (basis k) (hs k hk))
    (fun k hk => endpointFrame_mem_knownSpace Q N.frame W (Fin.last (n+1)) (basis k) (ht k hk))
  intro k hk
  have hb := physical_target_blind Q N hR (W (Fin.last (n+1))) r (P.β/8) hp Y (hY _) k hk
  linarith [P.β_pos]

end Bilevel.EndpointTransportResponse
