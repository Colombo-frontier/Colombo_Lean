import Bilevel.EndpointTransportCompletedReadout
import Bilevel.TransportHierarchyFrame

/-! One common finite completion for every terminal block of an actual
physical network. Each network vertex keeps its own global prefix; the
canonical terminal counter is exactly the restriction of that prefix. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation EndpointTransportMatrix ChiCarrier
  TransportHierarchy TransportNetwork ChiTreeProgress ChiHierarchyIndex

def paddedNetworkColumns {n D : ℕ} (T : ℕ) (hT : T≤D) (z : Latent (n+1) D)
    (v : Index n) (k : Fin (D+1)) : Block D :=
  if h : k.val<T then frame T hT z v ⟨k.val,h⟩ else 0

theorem paddedNetworkColumns_gram {n D : ℕ} (T : ℕ) (hT : T≤D)
    (z : Latent (n+1) D) (q : Index n → ℕ) (v : Index n)
    (a b : Fin (D+1)) (ha : a.val<min (q v) T) (hb : b.val<min (q v) T) :
    ⟪paddedNetworkColumns T hT z v a,paddedNetworkColumns T hT z v b⟫=
      if a=b then 1 else 0 := by
  have hat : a.val<T := (lt_min_iff.mp ha).2
  have hbt : b.val<T := (lt_min_iff.mp hb).2
  rw [paddedNetworkColumns,dif_pos hat,paddedNetworkColumns,dif_pos hbt]
  have hh := (orthonormal_iff_ite.mp (frame_orthonormal T hT z v))
    (⟨a.val,hat⟩:Fin T) (⟨b.val,hbt⟩:Fin T)
  simpa only [Fin.mk.injEq,Fin.ext_iff] using hh

theorem network_completed_rotations_exist {n D : ℕ} (T : ℕ) (hT : T≤D)
    (z : Latent (n+1) D) (q : Index n → ℕ) :
    ∃ Q : Rotations n (completionDimension D D),∀ v k,
      Q v (commonCompletionFrame D D (basis k))=
        completionBlockEquiv D D (completedColumn D (min (q v) T)
          (paddedNetworkColumns T hT z v)
          (LinearIsometryEquiv.refl ℝ (Space D)).toLinearIsometry k) :=
  completed_rotations_exist n D D (fun v => min (q v) T)
    (paddedNetworkColumns T hT z) (paddedNetworkColumns_gram T hT z q)

def canonicalCompletionFrame (counts : ℕ → ℕ) (J D : ℕ)
    (hT : capacity counts (J+1) 0≤D) (I : List ℕ) :
    Space (counts (J+1)) →ₗᵢ[ℝ] Space D :=
  blockFrame counts (J+1) (D+1) (canonicalList counts (J+1) I)
    (canonicalList_length counts (J+1) I) (canonical_legalFrom counts (J+1) I)
    (hT.trans (Nat.le_succ D))

def canonicalCompletionIndex (counts : ℕ → ℕ) (J D : ℕ)
    (hT : capacity counts (J+1) 0≤D) (I : List ℕ)
    (k : Fin (counts (J+1)+1)) : Fin (D+1) :=
  Fin.castLE (hT.trans (Nat.le_succ D)) (canonicalTerminalIndex counts (J+1) I k)

theorem canonicalCompletionFrame_basis (counts : ℕ → ℕ) (J D : ℕ)
    (hT : capacity counts (J+1) 0≤D) (I : List ℕ) (k : Fin (counts (J+1)+1)) :
    canonicalCompletionFrame counts J D hT I (basis k)=
      basis (canonicalCompletionIndex counts J D hT I k) := by
  exact blockFrame_basis counts (J+1) (D+1) (canonicalList counts (J+1) I)
    (canonicalList_length counts (J+1) I) (canonical_legalFrom counts (J+1) I)
    (hT.trans (Nat.le_succ D)) k

theorem canonicalCompletionIndex_prefix (counts : ℕ → ℕ) (J D : ℕ)
    (hT : capacity counts (J+1) 0≤D) (I : List ℕ) (q : ℕ)
    (k : Fin (counts (J+1)+1)) :
    (canonicalCompletionIndex counts J D hT I k).val<min q (capacity counts (J+1) 0) ↔
      k.val<canonicalCounter counts J q J I := by
  change (canonicalTerminalIndex counts (J+1) I k).val<min q (capacity counts (J+1) 0) ↔ _
  rw [lt_min_iff,and_iff_left (canonicalTerminalIndex counts (J+1) I k).isLt]
  exact (canonical_terminal_prefix counts J q I k).symm

theorem canonicalCompleted_endpoint_coordinates {n D : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (hT : capacity counts (J+1) 0≤D) (z : Latent (n+1) D) (q : Index n → ℕ)
    (Q : Rotations n (completionDimension D D))
    (hQ : ∀ v k,Q v (commonCompletionFrame D D (basis k))=
      completionBlockEquiv D D (completedColumn D (min (q v) (capacity counts (J+1) 0))
        (paddedNetworkColumns (capacity counts (J+1) 0) hT z v)
        (LinearIsometryEquiv.refl ℝ (Space D)).toLinearIsometry k))
    (v : Index n) (I : List ℕ) (data : Fin (counts (J+1)+1) → Physical n D)
    (hd : ∀ k,k.val<canonicalCounter counts J (q v) J I →
      data k=endpointFrame (physicalRotations z) (canonicalTerminalFrame counts (J+1) hT z I) v (basis k))
    (R : ℝ) (Y : Physical n D) :
    WrappedChain.coordinates (counts (J+1)) R
      (endpointFrame Q ((commonCompletionFrame D D).comp (canonicalCompletionFrame counts J D hT I)) v)
      (physicalMap (completionBlockInclusion D D) Y)=
        readout (counts (J+1)) (canonicalCounter counts J (q v) J I) R data Y := by
  apply completed_endpoint_coordinates (fun v => min (q v) (capacity counts (J+1) 0))
    (paddedNetworkColumns (capacity counts (J+1) 0) hT z) Q hQ
    (canonicalCompletionFrame counts J D hT I) (canonicalCompletionIndex counts J D hT I)
    (canonicalCompletionFrame_basis counts J D hT I) v _
    (canonicalCompletionIndex_prefix counts J D hT I (q v)) data ?_ R Y
  intro k hk
  rw [hd k hk]
  change insertion (n+2) v (physicalRotations z v (canonicalTerminalFrame counts (J+1) hT z I (basis k)))=_
  rw [canonical_terminal_network_column]
  congr 1
  have ht : (canonicalCompletionIndex counts J D hT I k).val<capacity counts (J+1) 0 :=
    (canonicalTerminalIndex counts (J+1) I k).isLt
  rw [paddedNetworkColumns,dif_pos ht]
  rfl

end Bilevel.EndpointTransportResponse
