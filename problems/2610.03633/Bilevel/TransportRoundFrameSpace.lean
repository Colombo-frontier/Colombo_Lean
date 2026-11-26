import Bilevel.TransportRoundFreshIdentity
import Bilevel.TransportRoundEdgeHistory

/-! Canonical full-frame and protected-prefix subspaces of the actual
network. The orthonormal basis used in the angle proof is exactly the given
finite frame, rather than an unrelated basis assumed by the execution. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportGeneratorStore TransportEdgePosterior OrthogonalAction
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def frameSpace {T : ℕ} (V : Fin T → E) : Submodule ℝ E := Submodule.span ℝ (Set.range V)

theorem spanBasis_orthonormal {T : ℕ} (V : Fin T → E) (hV : Orthonormal ℝ V) :
    Orthonormal ℝ (Basis.span hV.linearIndependent) := by
  have he : (Basis.span hV.linearIndependent : Fin T → frameSpace V) =
      fun i => ⟨V i,Submodule.subset_span (Set.mem_range_self i)⟩ := by
    funext i
    apply Subtype.ext
    exact Basis.span_apply hV.linearIndependent i
  rw [he]
  exact orthonormal_span hV

def frameBasis {T : ℕ} (V : Fin T → E) (hV : Orthonormal ℝ V) : OrthonormalBasis (Fin T) ℝ (frameSpace V) :=
  (Basis.span hV.linearIndependent).toOrthonormalBasis (spanBasis_orthonormal V hV)

theorem frameBasis_apply {T : ℕ} (V : Fin T → E) (hV : Orthonormal ℝ V) (i : Fin T) :
    (frameBasis V hV i : E)=V i := by
  have hh := congrArg (fun f : Fin T → frameSpace V => (f i : E))
    (Basis.coe_toOrthonormalBasis (Basis.span hV.linearIndependent) (spanBasis_orthonormal V hV))
  exact hh.trans (Basis.span_apply hV.linearIndependent i)

def protectedSpace {T : ℕ} (V : Fin T → E) (K : Finset (Fin T)) : Submodule ℝ E :=
  Submodule.span ℝ (V '' (K : Set (Fin T)))

theorem protectedSpace_mem {T : ℕ} (V : Fin T → E) (K : Finset (Fin T)) (i : Fin T) (hi : i∈K) :
    V i∈protectedSpace V K := Submodule.subset_span ⟨i,hi,rfl⟩

theorem protectedSpace_le_frame {T : ℕ} (V : Fin T → E) (K : Finset (Fin T)) :
    protectedSpace V K≤frameSpace V := by
  apply Submodule.span_mono
  rintro x ⟨i,_,rfl⟩
  exact ⟨i,rfl⟩

theorem protectedSpace_le {T : ℕ} (V : Fin T → E) (K : Finset (Fin T)) (S : Submodule ℝ E)
    (hS : ∀ i∈K, V i∈S) : protectedSpace V K≤S := by
  apply Submodule.span_le.mpr
  rintro x ⟨i,hi,rfl⟩
  exact hS i hi

theorem hardPairs_domain {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) :
    domain (hardPairs T hT e z)=frameSpace (frame T hT z (src e)) :=
  TransportControllerPairedStore.domain_pairs (frame T hT z (src e),frame T hT z (dst e))

theorem hardPairs_supported_actual {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) :
    Supports (hardPairs T hT e z) (z.2 e) := by
  apply (TransportControllerPairedStore.pairs_supported
    (frame T hT z (src e),frame T hT z (dst e)) (z.2 e)).mpr
  exact edge_frame T hT z e

def protectedDomain {D T : ℕ} (V : Fin T → Space D) (P : Pairs D) (K : Finset (Fin T)) :
    Submodule ℝ (Space D) := domain P⊔protectedSpace V K

theorem full_physical_domain {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D)
    (P : Pairs D) (K : Finset (Fin T)) :
    domain (hardPairs T hT e z++P)=frameSpace (frame T hT z (src e))⊔
      protectedDomain (frame T hT z (src e)) P K := by
  rw [domain_append,hardPairs_domain,protectedDomain]
  have hK := protectedSpace_le_frame (frame T hT z (src e)) K
  exact (sup_eq_left.mpr (hK.trans le_sup_left)).symm.trans (by ac_rfl)

theorem protectedDomain_le {D T : ℕ} (V : Fin T → Space D) (P : Pairs D) (K : Finset (Fin T))
    (S : Submodule ℝ (Space D)) (hP : domain P≤S) (hK : ∀ i∈K,V i∈S) :
    protectedDomain V P K≤S := sup_le hP (protectedSpace_le V K S hK)

theorem protectedDomain_image_le {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D)
    (P : Pairs D) (K : Finset (Fin T)) (W : Submodule ℝ (Space D))
    (hP : Supports P (z.2 e)) (hPW : range P≤W) (hK : ∀ i∈K,frame T hT z (dst e) i∈W) :
    (protectedDomain (frame T hT z (src e)) P K).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap≤W := by
  rw [protectedDomain,Submodule.map_sup,map_domain_eq_range P (z.2 e) hP]
  apply sup_le hPW
  rw [protectedSpace,Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro x ⟨y,⟨i,hi,rfl⟩,rfl⟩
  change z.2 e • frame T hT z (src e) i∈W
  rw [edge_frame]
  exact hK i hi

end Bilevel.TransportRound
