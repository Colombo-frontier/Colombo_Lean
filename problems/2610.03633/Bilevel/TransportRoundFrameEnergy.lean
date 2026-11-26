import Bilevel.TransportRoundFrameSpace

/-! The paired-monitor energy implication for an actual finite orthonormal
frame and either orientation of a fixed orthogonal map. This is the shared
deterministic primitive for the forward and reverse executed blocks. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportEdgePosterior OrthogonalAction ProjectionGeometry TransportObserver
set_option maxHeartbeats 800000

def framePairs {D T : ℕ} (V : Fin T → Space D) (O : OrthogonalHaar.Group D) : Pairs D :=
  TransportControllerPairedStore.pairs (V,fun i => O • V i)

theorem framePairs_domain {D T : ℕ} (V : Fin T → Space D) (O : OrthogonalHaar.Group D) :
    domain (framePairs V O)=frameSpace V := TransportControllerPairedStore.domain_pairs _

theorem frame_full_physical_domain {D T : ℕ} (V : Fin T → Space D) (O : OrthogonalHaar.Group D)
    (P : Pairs D) (K : Finset (Fin T)) :
    domain (framePairs V O++P)=frameSpace V⊔protectedDomain V P K := by
  rw [domain_append,framePairs_domain,protectedDomain]
  have hK := protectedSpace_le_frame V K
  exact (sup_eq_left.mpr (hK.trans le_sup_left)).symm.trans (by ac_rfl)

theorem frame_protectedDomain_image_le {D T : ℕ} (V : Fin T → Space D) (O : OrthogonalHaar.Group D)
    (P : Pairs D) (K : Finset (Fin T)) (W : Submodule ℝ (Space D))
    (hP : Supports P O) (hPW : range P≤W) (hK : ∀ i∈K,O • V i∈W) :
    (protectedDomain V P K).map (isometry D O).toLinearEquiv.toLinearMap≤W := by
  rw [protectedDomain,Submodule.map_sup,map_domain_eq_range P O hP]
  apply sup_le hPW
  rw [protectedSpace,Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro x ⟨y,⟨i,hi,rfl⟩,rfl⟩
  exact hK i hi

theorem frame_block_energy {D T : ℕ} (V : Fin T → Space D) (hV : Orthonormal ℝ V)
    (O : OrthogonalHaar.Group D) (P : Pairs D) (hP : Supports P O) (S F W : Submodule ℝ (Space D))
    (K I : Finset (Fin T)) (hIK : I⊆Finset.univ\K)
    (hPS : domain P≤S) (hFS : F≤S) (hKsrc : ∀ i∈K,V i∈S)
    (hPW : range P≤W) (hKdst : ∀ i∈K,O • V i∈W)
    {e : ℝ} (he : frameEnergy S V (Finset.univ\K)≤e) (hsmall : e≤(1:ℝ)/4096)
    (hgood : ¬ TransportControllerEdge.angleBad W
      (residualSpace (domain (framePairs V O++P)) (residualSpace (protectedDomain V P K) F)) O) :
    frameEnergy (W⊔F.map (isometry D O).toLinearEquiv.toLinearMap) (fun i => O • V i) I-
      frameEnergy W (fun i => O • V i) I ≤ 8*(e+frameEnergy W (fun i => O • V i) I) := by
  let H := frameSpace V
  let A := protectedDomain V P K
  let Kspace := protectedSpace V K
  let b := frameBasis V hV
  have hb : (fun i => (b i : Space D))=V := funext (frameBasis_apply V hV)
  have hK : ∀ i∈K, (b i : Space D)∈Kspace := by
    intro i hi
    rw [show (b i : Space D)=V i from congrFun hb i]
    exact protectedSpace_mem V K i hi
  have hs : frameEnergy S (fun i => (b i : Space D)) (Finset.univ\K)≤e := by
    rw [hb]
    exact he
  have hh := protected_energy_of_paired_monitor (framePairs V O++P) H A S F W Kspace b K I hIK
    (show Kspace≤A from le_sup_right) (protectedSpace_le_frame V K) hK
    (protectedDomain_le V P K S hPS hKsrc) hFS (frame_full_physical_domain V O P K) hs hsmall O hgood
  have hAW := frame_protectedDomain_image_le V O P K W hP hPW hKdst
  rw [transported_residual_merge (isometry D O) A F W hAW] at hh
  have hV' : (fun i => O • (b i : Space D))=(fun i => O • V i) := by
    funext i
    rw [show (b i : Space D)=V i from congrFun hb i]
  rw [hV'] at hh
  exact hh

def swapPairs {D : ℕ} (P : Pairs D) : Pairs D := P.map Prod.swap

theorem swapPairs_domain {D : ℕ} (P : Pairs D) : domain (swapPairs P)=range P := by
  induction P with
  | nil => rfl
  | cons pair P ih =>
    change domain (swapPairs P)⊔Submodule.span ℝ {pair.2}=range P⊔Submodule.span ℝ {pair.2}
    rw [ih]

theorem swapPairs_range {D : ℕ} (P : Pairs D) : range (swapPairs P)=domain P := by
  induction P with
  | nil => rfl
  | cons pair P ih =>
    change range (swapPairs P)⊔Submodule.span ℝ {pair.1}=domain P⊔Submodule.span ℝ {pair.1}
    rw [ih]

theorem swapPairs_supported {D : ℕ} (P : Pairs D) (O : OrthogonalHaar.Group D) (hP : Supports P O) :
    Supports (swapPairs P) O⁻¹ := by
  induction P with
  | nil => trivial
  | cons pair P ih =>
    change O⁻¹ • pair.2=pair.1 ∧ Supports (swapPairs P) O⁻¹
    refine ⟨?_,ih hP.2⟩
    rw [← hP.1,inv_smul_smul]

end Bilevel.TransportRound
