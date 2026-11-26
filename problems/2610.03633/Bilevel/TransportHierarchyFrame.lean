import Bilevel.TransportHierarchyOrdinal
import Bilevel.TransportNetworkPhysical
import Bilevel.ChiCanonicalHierarchy
import Bilevel.ChiSourceAuxiliaryFrame

/-! Deepest hierarchy frames are disjoint lexicographic blocks of the one
network frame. Ancestor/macro frames remain separate auxiliary variables.
All invalid list indices use the same canonicalization for frame and count. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.TransportHierarchy
open ChiTreeProgress ChiHierarchyIndex ChiBoundedChain ChiHierarchyHaar
  EuclideanGaussian TransportNetwork EndpointTransportResponse

set_option maxHeartbeats 700000

def blockLinear (counts : ℕ → ℕ) (d D : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (hD : capacity counts d 0≤D) :
    ChiBoundedChain.Space (counts d) →L[ℝ] EuclideanGaussian.Space D :=
  ∑ k : Fin (counts d+1),(EuclideanSpace.proj (𝕜:=ℝ) k).smulRight
    (EuclideanSpace.single (Fin.castLE hD (terminalIndex counts d I hI hlegal k)) 1)

theorem blockLinear_basis (counts : ℕ → ℕ) (d D : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (hD : capacity counts d 0≤D)
    (k : Fin (counts d+1)) :
    blockLinear counts d D I hI hlegal hD (basis k)=
      EuclideanSpace.single (Fin.castLE hD (terminalIndex counts d I hI hlegal k)) 1 := by
  simp [blockLinear,ContinuousLinearMap.sum_apply,basis,EuclideanSpace.single_apply]

def blockFrame (counts : ℕ → ℕ) (d D : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (hD : capacity counts d 0≤D) :
    ChiBoundedChain.Space (counts d) →ₗᵢ[ℝ] EuclideanGaussian.Space D :=
  (blockLinear counts d D I hI hlegal hD).toLinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin (counts d+1)) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin (counts d+1)) ℝ).orthonormal (by
      have he : ((blockLinear counts d D I hI hlegal hD).toLinearMap ∘
          (EuclideanSpace.basisFun (Fin (counts d+1)) ℝ).toBasis)=
          (fun k : Fin (counts d+1) => EuclideanSpace.single
            (Fin.castLE hD (terminalIndex counts d I hI hlegal k)) (1:ℝ)) := by
        funext k
        rw [Function.comp_apply]
        change blockLinear counts d D I hI hlegal hD ((EuclideanSpace.basisFun (Fin (counts d+1)) ℝ) k)=_
        rw [EuclideanSpace.basisFun_apply]
        exact blockLinear_basis counts d D I hI hlegal hD k
      rw [he]
      exact EuclideanSpace.orthonormal_single.comp _
        ((Fin.castLE_injective hD).comp (terminalIndex_injective counts d I hI hlegal)))

theorem blockFrame_basis (counts : ℕ → ℕ) (d D : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (hD : capacity counts d 0≤D)
    (k : Fin (counts d+1)) :
    blockFrame counts d D I hI hlegal hD (basis k)=
      EuclideanSpace.single (Fin.castLE hD (terminalIndex counts d I hI hlegal k)) 1 :=
  blockLinear_basis counts d D I hI hlegal hD k

theorem block_network_column {n D : ℕ} (counts : ℕ → ℕ) (d : ℕ) (I : List ℕ)
    (hI : I.length=d) (hlegal : LegalFrom counts 0 I) (hD : capacity counts d 0≤D)
    (z : Latent (n+1) D) (v : EndpointTransportMatrix.Index n) (k : Fin (counts d+1)) :
    physicalRotations z v (terminalBaseFrame z (blockFrame counts d D I hI hlegal hD) (basis k))=
      frame (capacity counts d 0) hD z v (terminalIndex counts d I hI hlegal k) := by
  rw [physical_terminal_frame,blockFrame_basis]
  simp only [TransportNetwork.frame,EuclideanSpace.basisFun_apply]

def canonicalTerminalIndex (counts : ℕ → ℕ) (d : ℕ) (I : List ℕ) (k : Fin (counts d+1)) :
    Fin (capacity counts d 0) :=
  terminalIndex counts d (canonicalList counts d I) (canonicalList_length counts d I)
    (canonical_legalFrom counts d I) k

def canonicalTerminalFrame {n D : ℕ} (counts : ℕ → ℕ) (d : ℕ)
    (hD : capacity counts d 0≤D) (z : Latent (n+1) D) (I : List ℕ) :
    ChiBoundedChain.Space (counts d) →ₗᵢ[ℝ] EuclideanGaussian.Space D :=
  terminalBaseFrame z (blockFrame counts d D (canonicalList counts d I)
    (canonicalList_length counts d I) (canonical_legalFrom counts d I) hD)

theorem canonical_terminal_prefix (counts : ℕ → ℕ) (J q : ℕ) (I : List ℕ)
    (k : Fin (counts (J+1)+1)) :
    k.val<canonicalCounter counts J q J I ↔ (canonicalTerminalIndex counts (J+1) I k).val<q := by
  rw [canonicalCounter,dif_pos le_rfl]
  exact counter_column_iff counts (J+1) q (canonicalList counts (J+1) I)
    (canonicalList_length counts (J+1) I) (canonical_legalFrom counts (J+1) I) k

theorem canonical_terminal_network_column {n D : ℕ} (counts : ℕ → ℕ) (d : ℕ)
    (hD : capacity counts d 0≤D) (z : Latent (n+1) D) (I : List ℕ)
    (v : EndpointTransportMatrix.Index n) (k : Fin (counts d+1)) :
    physicalRotations z v (canonicalTerminalFrame counts d hD z I (basis k))=
      frame (capacity counts d 0) hD z v (canonicalTerminalIndex counts d I k) :=
  block_network_column counts d (canonicalList counts d I) (canonicalList_length counts d I)
    (canonical_legalFrom counts d I) hD z v k

end Bilevel.TransportHierarchy
