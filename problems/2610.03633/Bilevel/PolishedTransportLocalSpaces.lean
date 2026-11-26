import Bilevel.PolishedTransportMaximum
import Bilevel.TransportRoundBatchEnergy

/-!
The source's edge-local spaces, with the complement of the OLD SOURCE
protected set tracked in both endpoint frames. In particular this is not
the post-round global future set at the source endpoint.
-/
noncomputable section
namespace Bilevel.PolishedTransportLocalSpaces
open EuclideanGaussian ProjectionGeometry TransportObserver TransportEdgePosterior
  OrthogonalAction TransportNetwork TransportRound
set_option maxHeartbeats 1000000

def sourceInitial {n D m T : ℕ} (hT : T ≤ D) (t : ℕ) (g : Generators n D m)
    (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n) : Submodule ℝ (Space D) :=
  protectedDomain (frame T hT z (src e)) (P e) (oldProtected T t (src e)) ⊔ known g (src e)

def destinationInitial {n D m T : ℕ} (hT : T ≤ D) (t : ℕ) (g : Generators n D m)
    (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n) : Submodule ℝ (Space D) :=
  protectedDomain (frame T hT z (dst e)) (swapPairs (P e)) (oldProtected T t (src e)) ⊔ known g (dst e)

def destinationForward {n D m T : ℕ} (hT : T ≤ D) (t : ℕ) (g : Generators n D m)
    (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n) : Submodule ℝ (Space D) :=
  destinationInitial hT t g z P e ⊔
    (known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap

def sourceReverse {n D m T : ℕ} (hT : T ≤ D) (t : ℕ) (g : Generators n D m)
    (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n) : Submodule ℝ (Space D) :=
  sourceInitial hT t g z P e ⊔
    (known g (dst e)).map (isometry D ((z.2 e)⁻¹)).toLinearEquiv.toLinearMap

theorem sourceInitial_eq_frozen {n D m T : ℕ} (hT : T ≤ D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n)
    (hPS : domain (P e) ≤ known g (src e))
    (hprefix : ∀ v i,Protected t v i → frame T hT z v i ∈ known g v) :
    sourceInitial hT t g z P e=known g (src e) := by
  apply sup_eq_right.mpr
  apply protectedDomain_le _ _ _ _ hPS
  intro i hi
  apply hprefix
  simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi

theorem destinationInitial_le_postGrant {n D m T : ℕ} (hT : T ≤ D) (hn : 0 < n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n)
    (hPD : range (P e) ≤ known g (dst e))
    (hprefix : ∀ v i,Protected t v i → frame T hT z v i ∈ known g v) :
    destinationInitial hT t g z P e ≤ known (postGrant T hT t g z) (dst e) := by
  apply sup_le _ (postGrant_keeps T hT t g z (dst e))
  apply protectedDomain_le
  · rw [swapPairs_domain]
    exact hPD.trans (postGrant_keeps T hT t g z (dst e))
  · intro i hi
    apply postGrant_prefix T hT hn t g z hprefix
    apply paired_dst_post t e i
    simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi

theorem destinationForward_le_execute {n D m T : ℕ} (hT : T ≤ D) (hn : 0 < n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n)
    (hPD : range (P e) ≤ known g (dst e))
    (hprefix : ∀ v i,Protected t v i → frame T hT z v i ∈ known g v) :
    destinationForward hT t g z P e ≤ known (execute g z) (dst e) :=
  sup_le ((destinationInitial_le_postGrant hT hn t g z P e hPD hprefix).trans
    (postGrant_le_execute T hT t g z hprefix (dst e))) (forward_whole_space g z e)

theorem destinationForward_energy {n D m T : ℕ} (hT : T ≤ D) (hn : 0 < n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n)
    (hPD : range (P e) ≤ known g (dst e))
    (hprefix : ∀ v i,Protected t v i → frame T hT z v i ∈ known g v) :
    frameEnergy (destinationForward hT t g z P e) (frame T hT z (dst e)) (oldFuture T t (src e)) ≤
      TransportRoundEnergy.total (known (execute g z)) (frame T hT z) (postFuture T t) := by
  apply (frameEnergy_mono (destinationForward_le_execute hT hn t g z P e hPD hprefix) _ _).trans
  rw [← postFuture_dst T t e]
  exact TransportRoundEnergy.row_le_total _ _ _ (dst e)

/-- Every partial accumulation order uses a subspace of the same complete
frozen batch output. Its global target set is the post-grant complement. -/
theorem partial_global_energy {n D m T : ℕ} (hT : T ≤ D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (W : Known n D)
    (hW : ∀ v,W v ≤ known (execute g z) v) (v : Vertex n) :
    frameEnergy (W v) (frame T hT z v) (postFuture T t v) ≤
      TransportRoundEnergy.total (known (execute g z)) (frame T hT z) (postFuture T t) :=
  (frameEnergy_mono (hW v) _ _).trans (TransportRoundEnergy.row_le_total _ _ _ v)

theorem reverse_monitor_at {n D m T : ℕ} (hT : T ≤ D) (t : ℕ) (g : Generators n D m)
    (z : Latent n D) (P : Edge n → Pairs D) (es : List (Edge n)) (W : Known n D)
    (e : Edge n) (he : e ∈ es) (hgood : ¬reverseFailure hT t g z P es W) :
    ∃ W' : Known n D,(∀ v,W v ≤ W' v) ∧ ¬reverseMonitor hT t g z P W' e := by
  induction es generalizing W with
  | nil => simp only [List.not_mem_nil] at he
  | cons f es ih =>
    have hg := not_or.mp hgood
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨W,fun _ => le_rfl,hg.1⟩
    · obtain ⟨W',hW',hmon⟩ := ih (mergeBlock W (reverseBlock g z f)) he hg.2
      exact ⟨W',fun v => (le_mergeBlock W (reverseBlock g z f) v).trans (hW' v),hmon⟩

/-- The local reverse source tracks the larger OLD-source complement.
Its source-energy premise follows from the actual final destination row. -/
theorem sourceReverse_energy {n D m T : ℕ} (hT : T ≤ D) (_hn : 0 < n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n)
    (hP : Supports (P e) (z.2 e)) (hPS : domain (P e) ≤ known g (src e))
    (hPD : range (P e) ≤ known g (dst e))
    (hprefix : ∀ v i,Protected t v i → frame T hT z v i ∈ known g v)
    (W : Known n D) (hW : known (postGrant T hT t g z) (src e) ≤ W (src e))
    {Z : ℝ} (hsmall : Z ≤ (1 : ℝ)/4096)
    (hsrc : frameEnergy (known g (src e)) (frame T hT z (src e)) (oldFuture T t (src e)) ≤ Z)
    (hdst : frameEnergy (destinationForward hT t g z P e) (frame T hT z (dst e))
      (oldFuture T t (src e)) ≤ Z)
    (hgood : ¬reverseMonitor hT t g z P W e) :
    frameEnergy (sourceReverse hT t g z P e) (frame T hT z (src e)) (oldFuture T t (src e)) ≤ 17*Z := by
  let V := frame T hT z (dst e)
  let K := oldProtected T t (src e)
  let S := destinationForward hT t g z P e
  let R := swapPairs (forwardPairs e g z++P e)
  have hphys : Supports R ((z.2 e)⁻¹) :=
    swapPairs_supported _ _ ((supports_append _ _ _).mpr ⟨forwardPairs_supported e g z,hP⟩)
  have hdom : domain R ≤ S := by
    rw [swapPairs_domain,range_append,forwardPairs_range]
    exact sup_le le_sup_right (hPD.trans (le_sup_right.trans le_sup_left))
  have hFd : known g (dst e) ≤ S := le_sup_right.trans le_sup_left
  have hran : range R ≤ known g (src e) := by
    rw [swapPairs_range,domain_append,forwardPairs_domain]
    exact sup_le le_rfl hPS
  have hKsrc : ∀ i ∈ K,V i ∈ S := by
    intro i hi
    have hin : V i ∈ protectedDomain V (swapPairs (P e)) K :=
      (show protectedSpace V K ≤ protectedDomain V (swapPairs (P e)) K from le_sup_right)
        (protectedSpace_mem V K i hi)
    have hin' : V i ∈ destinationInitial hT t g z P e :=
      (show protectedDomain V (swapPairs (P e)) K ≤ destinationInitial hT t g z P e from le_sup_left) hin
    exact (show destinationInitial hT t g z P e ≤ S from le_sup_left) hin'
  have hKdst : ∀ i ∈ K,(z.2 e)⁻¹ • V i ∈ known g (src e) := by
    intro i hi
    rw [inverse_edge_frame]
    apply hprefix
    simpa only [K,oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hgoodLocal := PolishedTransportMaximum.good_angle_smaller_destination
    (known g (src e)) (W (src e)) _ ((z.2 e)⁻¹)
    ((postGrant_keeps T hT t g z (src e)).trans hW) hgood
  have hg : ¬TransportControllerEdge.angleBad (known g (src e))
      (residualSpace (domain (framePairs V ((z.2 e)⁻¹)++R))
        (residualSpace (protectedDomain V R K) (known g (dst e)))) ((z.2 e)⁻¹) := by
    simpa only [V,R,K,inverse_framePairs,reverseMonitor] using hgoodLocal
  have hh := frame_block_energy V (frame_orthonormal T hT z (dst e)) ((z.2 e)⁻¹)
    R hphys S (known g (dst e)) (known g (src e)) K (oldFuture T t (src e))
    (by rw [oldFuture_eq_complement]) hdom hFd hKsrc hran hKdst
    (by simpa only [S,V,K,← oldFuture_eq_complement] using hdst) hsmall hg
  have hframe : (fun i => (z.2 e)⁻¹ • V i)=frame T hT z (src e) :=
    funext (inverse_edge_frame hT e z)
  rw [hframe] at hh
  rw [sourceReverse,sourceInitial_eq_frozen hT t g z P e hPS hprefix]
  linarith

/-- All four actual source-local spaces in one genuine frozen batch.
No assumption about their post-forward/reverse energy is present. -/
theorem executed_batch_local_energies {n D m T : ℕ} (hT : T ≤ D) (hn : 0 < n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D)
    (hP : ∀ e,Supports (P e) (z.2 e))
    (hPS : ∀ e,domain (P e) ≤ known g (src e)) (hPD : ∀ e,range (P e) ≤ known g (dst e))
    (hprefix : ∀ v i,Protected t v i → frame T hT z v i ∈ known g v)
    (hbudget : batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) ≤ (1 : ℝ)/4096)
    (hgood : ¬batchFailure hT t g z P) (e : Edge n) :
    let Z := batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)
    let I := oldFuture T t (src e)
    frameEnergy (sourceInitial hT t g z P e) (frame T hT z (src e)) I ≤ Z ∧
    frameEnergy (destinationInitial hT t g z P e) (frame T hT z (dst e)) I ≤ Z ∧
    frameEnergy (destinationForward hT t g z P e) (frame T hT z (dst e)) I ≤ Z ∧
    frameEnergy (sourceReverse hT t g z P e) (frame T hT z (src e)) I ≤ 17*Z := by
  dsimp only
  let Z := batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)
  have hbatch := executed_batch_energy hT hn t g z P hP hPS hPD hprefix hbudget hgood
  have hfrozen : TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) ≤ Z := by
    have hh := mul_le_mul_of_nonneg_right (batchFactor_ge_one n)
      (TransportRoundEnergy.total_nonneg (known g) (frame T hT z) (oldFuture T t))
    simpa only [one_mul] using hh
  have hs : frameEnergy (known g (src e)) (frame T hT z (src e)) (oldFuture T t (src e)) ≤ Z :=
    (TransportRoundEnergy.row_le_total _ _ _ (src e)).trans hfrozen
  have hd := (destinationForward_energy hT hn t g z P e (hPD e) hprefix).trans hbatch
  obtain ⟨W,hW,hmon⟩ := reverse_monitor_at hT t g z P (List.ofFn (fun e : Edge n => e))
    (forwardLedger g z (known (postGrant T hT t g z))) e (List.mem_ofFn.mpr ⟨e,rfl⟩)
    (not_or.mp hgood).2
  have hSW : known (postGrant T hT t g z) (src e) ≤ W (src e) :=
    (le_mergeBlocks (forwardBlocks g z) _ (src e)).trans (hW (src e))
  have hr := sourceReverse_energy hT hn t g z P e (hP e) (hPS e) (hPD e) hprefix W hSW hbudget hs hd hmon
  refine ⟨?_,?_,hd,hr⟩
  · rw [sourceInitial_eq_frozen hT t g z P e (hPS e) hprefix]
    exact hs
  · exact (frameEnergy_mono (le_sup_left : destinationInitial hT t g z P e ≤
      destinationForward hT t g z P e) _ _).trans hd

end Bilevel.PolishedTransportLocalSpaces
