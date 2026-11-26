import Bilevel.TransportRoundFrameEnergy
import Bilevel.TransportRoundForwardEnergy
import Bilevel.TransportControllerReversePolicy

/-! Reverse innovation after the whole forward block of the same edge has
updated its physical pairs. The source ledger is the post-prefix destination
space containing those actual forward outputs. Frozen reverse probes remain
the old destination generators, never new forward outputs. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior OrthogonalAction ProjectionGeometry TransportObserver
set_option maxHeartbeats 800000

theorem inverse_edge_frame {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) (i : Fin T) :
    (z.2 e)⁻¹ • frame T hT z (dst e) i=frame T hT z (src e) i := by
  rw [← edge_frame T hT z e i,inv_smul_smul]

theorem inverse_framePairs {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) :
    framePairs (frame T hT z (dst e)) ((z.2 e)⁻¹)=reverseHardPairs T hT e z := by
  unfold framePairs TransportControllerPairedStore.pairs reverseHardPairs
  congr 1
  funext i
  exact Prod.ext rfl (inverse_edge_frame hT e z i)

theorem forwardPairs_supported {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) :
    Supports (forwardPairs e g z) (z.2 e) := by
  apply (TransportControllerPairedStore.pairs_supported (g (src e),fun i => z.2 e • g (src e) i) _).mpr
  intro i
  rfl

theorem reverse_frozen_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (edge : Edge n) (P : Pairs D)
    (hP : Supports P (z.2 edge))
    (hPS : domain P≤known g (src edge)) (hPD : range P≤known g (dst edge))
    (hprefix : ∀ v i, Protected t v i → frame T hT z v i∈known g v)
    (S W : Submodule ℝ (Space D))
    (hS : known (postGrant T hT t g z) (dst edge)⊔
      (known g (src edge)).map (isometry D (z.2 edge)).toLinearEquiv.toLinearMap≤S)
    (hW : known (postGrant T hT t g z) (src edge)≤W)
    {e : ℝ} (he : frameEnergy S (frame T hT z (dst edge)) (postFuture T t (dst edge))≤e)
    (hsmall : e≤(1:ℝ)/4096)
    (hgood : ¬TransportControllerEdge.angleBad W
      (residualSpace (domain (reverseHardPairs T hT edge z++swapPairs (forwardPairs edge g z++P)))
        (residualSpace (protectedDomain (frame T hT z (dst edge)) (swapPairs (forwardPairs edge g z++P))
          (oldProtected T t (src edge))) (known g (dst edge)))) ((z.2 edge)⁻¹)) :
    frameEnergy (W⊔(known g (dst edge)).map (isometry D ((z.2 edge)⁻¹)).toLinearEquiv.toLinearMap)
        (frame T hT z (src edge)) (postFuture T t (src edge))-
      frameEnergy W (frame T hT z (src edge)) (postFuture T t (src edge)) ≤
        8*(e+frameEnergy W (frame T hT z (src edge)) (postFuture T t (src edge))) := by
  classical
  have hS0 : known g (dst edge)≤S :=
    (postGrant_keeps T hT t g z (dst edge)).trans (le_sup_left.trans hS)
  have hW0 : known g (src edge)≤W := (postGrant_keeps T hT t g z (src edge)).trans hW
  have hphys : Supports (swapPairs (forwardPairs edge g z++P)) ((z.2 edge)⁻¹) :=
    swapPairs_supported _ _ ((supports_append _ _ _).mpr ⟨forwardPairs_supported edge g z,hP⟩)
  have hdom : domain (swapPairs (forwardPairs edge g z++P))≤S := by
    rw [swapPairs_domain,range_append,forwardPairs_range]
    exact sup_le (le_sup_right.trans hS) (hPD.trans hS0)
  have hran : range (swapPairs (forwardPairs edge g z++P))≤W := by
    rw [swapPairs_range,domain_append,forwardPairs_domain]
    exact sup_le hW0 (hPS.trans hW0)
  have hKsrc : ∀ i∈oldProtected T t (src edge),frame T hT z (dst edge) i∈S := by
    intro i hi
    apply (show known (postGrant T hT t g z) (dst edge)≤S from le_sup_left.trans hS)
    apply postGrant_prefix T hT hn t g z hprefix
    apply paired_dst_post t edge i
    simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hKdst : ∀ i∈oldProtected T t (src edge),(z.2 edge)⁻¹ • frame T hT z (dst edge) i∈W := by
    intro i hi
    rw [inverse_edge_frame]
    apply hW0
    apply hprefix
    simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hI : postFuture T t (src edge)⊆Finset.univ\oldProtected T t (src edge) := by
    rw [← oldFuture_eq_complement]
    exact postFuture_src_subset T t edge
  have henergy : frameEnergy S (frame T hT z (dst edge)) (Finset.univ\oldProtected T t (src edge))≤e := by
    rw [← oldFuture_eq_complement,← postFuture_dst]
    exact he
  have hg : ¬TransportControllerEdge.angleBad W
      (residualSpace (domain (framePairs (frame T hT z (dst edge)) ((z.2 edge)⁻¹)++swapPairs (forwardPairs edge g z++P)))
        (residualSpace (protectedDomain (frame T hT z (dst edge)) (swapPairs (forwardPairs edge g z++P))
          (oldProtected T t (src edge))) (known g (dst edge)))) ((z.2 edge)⁻¹) := by
    rw [inverse_framePairs]
    exact hgood
  have hh := frame_block_energy (frame T hT z (dst edge)) (frame_orthonormal T hT z (dst edge))
    ((z.2 edge)⁻¹) _ hphys S (known g (dst edge)) W (oldProtected T t (src edge)) (postFuture T t (src edge))
    hI hdom hS0 hKsrc hran hKdst henergy hsmall hg
  have hframe : (fun i => (z.2 edge)⁻¹ • frame T hT z (dst edge) i)=frame T hT z (src edge) :=
    funext (inverse_edge_frame hT edge z)
  rw [hframe] at hh
  exact hh

end Bilevel.TransportRound
