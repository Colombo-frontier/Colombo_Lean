import Bilevel.TransportRoundFrameSpace
import Bilevel.TransportRoundGrantFacts

/-! The protected energy estimate instantiated with the actual network
frame and executed physical edge history. The final theorem concerns the
whole frozen forward block at a genuine run state; paired-domain and named
prefix geometry are derived, rather than left as assumptions. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior OrthogonalAction ProjectionGeometry TransportObserver
set_option maxHeartbeats 800000

theorem edge_block_energy {n D T : ℕ} (hT : T≤D) (edge : Edge n) (z : Latent n D)
    (P : Pairs D) (hP : Supports P (z.2 edge)) (S F W : Submodule ℝ (Space D))
    (K I : Finset (Fin T)) (hIK : I⊆Finset.univ\K)
    (hPS : domain P≤S) (hFS : F≤S) (hKsrc : ∀ i∈K,frame T hT z (src edge) i∈S)
    (hPW : range P≤W) (hKdst : ∀ i∈K,frame T hT z (dst edge) i∈W)
    {e : ℝ} (he : frameEnergy S (frame T hT z (src edge)) (Finset.univ\K)≤e)
    (hsmall : e≤(1:ℝ)/4096)
    (hgood : ¬ TransportControllerEdge.angleBad W
      (residualSpace (domain (hardPairs T hT edge z++P))
        (residualSpace (protectedDomain (frame T hT z (src edge)) P K) F)) (z.2 edge)) :
    frameEnergy (W⊔F.map (isometry D (z.2 edge)).toLinearEquiv.toLinearMap) (frame T hT z (dst edge)) I-
      frameEnergy W (frame T hT z (dst edge)) I ≤
        8*(e+frameEnergy W (frame T hT z (dst edge)) I) := by
  let V := frame T hT z (src edge)
  let H := frameSpace V
  let A := protectedDomain V P K
  let Kspace := protectedSpace V K
  let b := frameBasis V (frame_orthonormal T hT z (src edge))
  have hb : (fun i => (b i : Space D))=V :=
    funext (frameBasis_apply V (frame_orthonormal T hT z (src edge)))
  have hK : ∀ i∈K, (b i : Space D)∈Kspace := by
    intro i hi
    rw [show (b i : Space D)=V i from congrFun hb i]
    exact protectedSpace_mem V K i hi
  have hs : frameEnergy S (fun i => (b i : Space D)) (Finset.univ\K)≤e := by
    rw [hb]
    exact he
  have hh := protected_energy_of_paired_monitor (hardPairs T hT edge z++P) H A S F W Kspace b K I hIK
    (show Kspace≤A from le_sup_right) (protectedSpace_le_frame V K) hK
    (protectedDomain_le V P K S hPS hKsrc) hFS (full_physical_domain hT edge z P K) hs hsmall (z.2 edge) hgood
  have hAW := protectedDomain_image_le hT edge z P K W hP hPW hKdst
  rw [transported_residual_merge (isometry D (z.2 edge)) A F W hAW] at hh
  have hV : (fun i => z.2 edge • (b i : Space D))=frame T hT z (dst edge) := by
    funext i
    rw [show (b i : Space D)=V i from congrFun hb i]
    exact edge_frame T hT z edge i
  rw [hV] at hh
  exact hh

def frozenAt {H : Type*} {n D p c m T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (t : ℕ) :
    Generators n D (size n p c m t+p) :=
  let st := run T hT choose respond names s z t
  augment st.2 (choose t st)

theorem runPairs_frozen_included {H : Type*} {n D p c m T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (edge : Edge n) (t : ℕ) :
    domain (runPairs hT choose respond names s z edge t)≤known (frozenAt hT choose respond names s z t) (src edge) ∧
      range (runPairs hT choose respond names s z edge t)≤known (frozenAt hT choose respond names s z t) (dst edge) := by
  have hh := runPairs_included hT choose respond names s z edge t
  dsimp only [frozenAt]
  rw [augment_span,augment_span]
  exact ⟨hh.1.trans le_sup_left,hh.2.trans le_sup_left⟩

theorem frozenAt_prefix {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) :
    ∀ v i, Protected t v i → frame T hT z v i∈
      known (frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t) v := by
  exact frozen_prefix T hT t _ _ z (run_prefix T hT hn choose respond memory z t)

theorem run_forward_energy {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) (edge : Edge n) (W : Submodule ℝ (Space D)) :
    let g := frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t
    let P := runPairs hT choose respond (prefixNames n T) (memory,seed T hT z) z edge t
    let K := oldProtected T t (src edge)
    let e := frameEnergy (known g (src edge)) (frame T hT z (src edge)) (oldFuture T t (src edge))
    known (postGrant T hT t g z) (dst edge)≤W → e≤(1:ℝ)/4096 →
    ¬TransportControllerEdge.angleBad W
      (residualSpace (domain (hardPairs T hT edge z++P))
        (residualSpace (protectedDomain (frame T hT z (src edge)) P K) (known g (src edge)))) (z.2 edge) →
    frameEnergy (W⊔(known g (src edge)).map (isometry D (z.2 edge)).toLinearEquiv.toLinearMap)
        (frame T hT z (dst edge)) (postFuture T t (dst edge))-
      frameEnergy W (frame T hT z (dst edge)) (postFuture T t (dst edge)) ≤
        8*(e+frameEnergy W (frame T hT z (dst edge)) (postFuture T t (dst edge))) := by
  classical
  dsimp only
  intro hW hsmall hgood
  have hpair := runPairs_frozen_included hT choose respond (prefixNames n T) (memory,seed T hT z) z edge t
  have hp := frozenAt_prefix hT hn choose respond memory z t
  apply edge_block_energy hT edge z _ (runPairs_supported hT choose respond (prefixNames n T) (memory,seed T hT z) z edge t)
    _ _ W _ _ _ hpair.1 le_rfl _ _ _ _ hsmall hgood
  · rw [postFuture_dst,oldFuture_eq_complement]
  · intro i hi
    apply hp
    simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  · exact hpair.2.trans ((postGrant_keeps T hT t _ z _).trans hW)
  · intro i hi
    apply hW
    apply postGrant_prefix T hT hn t _ z hp
    apply paired_dst_post t edge i
    simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  · rw [← oldFuture_eq_complement]

end Bilevel.TransportRound
