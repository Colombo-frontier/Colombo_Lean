import Bilevel.EndpointTransportPayload
import Bilevel.NearIdentityConfinement

/-! Every restricted physical point is target-blind from the target-layer
projection bound alone. The source endpoint may acquire a new column without
changing this estimate, because the full physical radial compression is a
scalar multiple of the queried physical vector. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive PrimitiveGeometry RadialWrapper

theorem physical_target_projection_bound {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hR : 0<N.radius) (W : Submodule ℝ (Block D)) [CompleteSpace W]
    (Y : Physical n D) (hY : Y (Fin.last (n+1))∈W) (k : Fin (N.n+1)) :
    |(physicalCoordinates Q N Y).snd k|≤
      (gamma n*N.radius)*‖W.orthogonalProjection (Q (Fin.last (n+1)) (N.frame (basis k)))‖ := by
  have hγ : 0<gamma n*N.radius := mul_pos (gamma_positive n) hR
  let j : Index n := Fin.last (n+1)
  let p : W := ⟨(compress (gamma n*N.radius) Y) j,by
    change scale (gamma n*N.radius) Y • Y j∈W
    exact W.smul_mem _ hY⟩
  have hi := NearIdentityConfinement.projected_inner_bound W (Q j (N.frame (basis k))) p
  have hn : ‖(p:Block D)‖≤gamma n*N.radius :=
    (PiLp.norm_apply_le (compress (gamma n*N.radius) Y) j).trans
      (compress_norm_le_radius _ hγ Y)
  change |targetReadout Q N.frame (compress (gamma n*N.radius) Y) k|≤_
  rw [(readout_coordinate Q N.frame _ k).2]
  exact hi.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem physical_target_blind {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hR : 0<N.radius) (W : Submodule ℝ (Block D)) [CompleteSpace W] (r : ℕ) (τ : ℝ)
    (hproj : ∀ k : Fin (N.n+1),r≤k.val →
      (gamma n*N.radius)*‖W.orthogonalProjection (Q (Fin.last (n+1)) (N.frame (basis k)))‖≤τ)
    (Y : Physical n D) (hY : Y (Fin.last (n+1))∈W) :
    ∀ k : Fin (N.n+1),r≤k.val → |(physicalCoordinates Q N Y).snd k|≤τ :=
  fun k hk => (physical_target_projection_bound Q N hR W Y hY k).trans (hproj k hk)

end Bilevel.EndpointTransportResponse
