import Bilevel.EndpointTransportQuadraticReachable
import Bilevel.EndpointTransportTargetProjection
import Bilevel.ChiCarrierProjectionBlind

/-! A current physical query and PREBATCH projection bounds imply the
complete depth-zero upper scalar germ. Only old target columns and the
globally reachable next source columns are used. -/
noncomputable section
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive
set_option autoImplicit false
set_option maxHeartbeats 900000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadraticCore_prefix_germ_of_projections {n D : ℕ} (Q : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℝ)
    (rM : ℕ) (r : Fin (M.n+1) → ℕ) (macroColumns : Fin (M.n+1) → E)
    (sourceColumns targetColumns : ∀ i : Fin (M.n+1),Fin ((G 0 [i.val]).n+1) → Physical n D)
    (hm : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hs : ∀ i,i.val≤rM → ∀ k : Fin ((G 0 [i.val]).n+1),k.val<r i+1 →
      sourceColumns i k=endpointFrame Q (G 0 [i.val]).frame 0 (basis k))
    (ht : ∀ i,∀ k : Fin ((G 0 [i.val]).n+1),k.val<r i →
      targetColumns i k=endpointFrame Q (G 0 [i.val]).frame (Fin.last (n+1)) (basis k))
    (hmw : 0<M.width) (hmR : 0<M.radius)
    (hh : ∀ I,0<(G 0 I).width) (hR : ∀ I,0<(G 0 I).radius)
    (hhp : ∀ I,0<(G 0 I).parentWidth) (hw : ∀ I,(G 0 I).width≤(G 0 I).parentWidth)
    (hwidth : ∀ I,(G 0 I).width=(G 0 []).width)
    (hfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r i≤(G 0 [i.val]).n)
    (WM : Submodule ℝ E) [CompleteSpace WM] (WT : Submodule ℝ (Block D)) [CompleteSpace WT]
    (z : Joint E (Physical n D)) (hzM : z.fst∈WM) (hzT : z.snd (Fin.last (n+1))∈WT)
    (hprojM : ∀ k : Fin (M.n+1),rM≤k.val →
      M.radius*‖WM.orthogonalProjection (M.frame (basis k))‖≤M.width/8)
    (hprojT : ∀ i,∀ k : Fin ((G 0 [i.val]).n+1),r i≤k.val →
      (EndpointTransportMatrix.gamma n*(G 0 [i.val]).radius)*
        ‖WT.orthogonalProjection (Q (Fin.last (n+1)) ((G 0 [i.val]).frame (basis k)))‖≤
          (G 0 [i.val]).width/8) :
    quadraticCore Q M ν G ρ R =ᶠ[𝓝 z]
      prefixQuadraticCore Q M ν G ρ R rM r macroColumns sourceColumns targetColumns := by
  let δ := min M.width (G 0 []).width/16
  have hδ : 0<δ := div_pos (lt_min hmw (hh [])) (by norm_num)
  have hδM : δ≤M.width/16 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδN (i : Fin (M.n+1)) : δ≤(G 0 [i.val]).width/16 := by
    rw [hwidth]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  apply quadraticCore_eventuallyEq_prefix_reachable Q M ν G ρ R rM r macroColumns sourceColumns targetColumns
    hm hs ht hmw (fun i => hh [i.val]) (fun i => hhp [i.val]) (fun i => hw [i.val]) hfuture z
    _ _ hmR (fun i => hR [i.val]) δ hδ hδM hδN
  · intro k hk
    have hb := (M.coordinate_projection_bound hmR WM ⟨z.fst,hzM⟩ k).trans (hprojM k hk)
    linarith
  · intro i k hk
    have hb := (physical_target_projection_bound Q (G 0 [i.val]) (hR [i.val]) WT z.snd hzT k).trans
      (hprojT i k hk)
    have hp := hh [i.val]
    linarith

end Bilevel.EndpointTransportResponse
