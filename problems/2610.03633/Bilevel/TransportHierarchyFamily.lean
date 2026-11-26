import Bilevel.TransportHierarchyFrame
import Bilevel.TransportHierarchyAuxiliarySchedule
import Bilevel.ChiCanonicalFrameFamily

/-! The concrete physical hard-family prior: independent Haar macro and
ancestor frames, and deepest frames as disjoint blocks of the single
transport network frame. All scalar geometry is unchanged. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiTreeProgress ChiHierarchyIndex ChiBoundedChain ChiHierarchyHaar
  EuclideanGaussian TransportNetwork EndpointTransportResponse OrthogonalAction
set_option maxHeartbeats 700000

abbrev PhysicalSample (counts : ℕ → ℕ) (J n D : ℕ) :=
  TransportNetworkAuxiliary.Sample (n+1) D (Fintype.card (FrameIndex counts J))

def auxiliaryOrientations {counts : ℕ → ℕ} {J n D : ℕ}
    (s : PhysicalSample counts J n D) : Orientations counts J D :=
  fun i => s.2 (enumerate counts J i)

theorem auxiliaryOrientations_measurable (counts : ℕ → ℕ) (J n D : ℕ) :
    Measurable (auxiliaryOrientations (counts:=counts) (J:=J) (n:=n) (D:=D)) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (enumerate counts J i)).comp measurable_snd

def physicalMacroFrame {counts : ℕ → ℕ} {J n D : ℕ}
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (s : PhysicalSample counts J n D) : ChiBoundedChain.Space (counts 0) →ₗᵢ[ℝ] EuclideanGaussian.Space D :=
  ChiHierarchyHaar.frame hAll (auxiliaryOrientations s) (Sum.inl ())

def physicalFamily {counts : ℕ → ℕ} {J n D : ℕ}
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (s : PhysicalSample counts J n D) (j : ℕ) (I : List ℕ) :
    ChiBoundedChain.Space (counts (j+1)) →ₗᵢ[ℝ] EuclideanGaussian.Space D := by
  classical
  by_cases h : j=J
  · subst j
    exact canonicalTerminalFrame counts (J+1) hT s.1 I
  · exact canonicalFamily hdim (auxiliaryOrientations s) j I

theorem physicalFamily_terminal {counts : ℕ → ℕ} {J n D : ℕ}
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (s : PhysicalSample counts J n D) (I : List ℕ) :
    physicalFamily hdim hT s J I=canonicalTerminalFrame counts (J+1) hT s.1 I := by
  simp [physicalFamily]

theorem physicalFamily_ancestor {counts : ℕ → ℕ} {J n D : ℕ}
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (s : PhysicalSample counts J n D) (j : ℕ) (hj : j<J) (I : List ℕ) :
    physicalFamily hdim hT s j I=
      ChiHierarchyHaar.frame hAll (auxiliaryOrientations s)
        (Sum.inr (canonicalNode counts J ⟨j,Nat.lt_succ_of_lt hj⟩ I)) := by
  rw [physicalFamily,dif_neg (ne_of_lt hj)]
  exact canonicalFamily_covered hdim hAll _ j hj.le I

theorem physicalMacroFrame_column_measurable {counts : ℕ → ℕ} {J n D : ℕ}
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D) (k : Fin (counts 0+1)) :
    Measurable (fun s : PhysicalSample counts J n D => physicalMacroFrame hAll s (basis k)) := by
  have h := (measurable_pi_apply k).comp
    ((measurable_pi_apply (Sum.inl () : FrameIndex counts J)).comp
      ((columns_measurable hAll).comp (auxiliaryOrientations_measurable counts J n D)))
  have he : (fun s : PhysicalSample counts J n D => physicalMacroFrame hAll s (basis k))=
      (fun s => columns hAll (auxiliaryOrientations s) (Sum.inl ()) k) := by
    funext s
    exact ChiHierarchyHaar.frame_basis hAll (auxiliaryOrientations s) (Sum.inl ()) k
  rw [he]
  exact h

theorem physicalFamily_column_measurable {counts : ℕ → ℕ} {J n D : ℕ}
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (j : ℕ) (I : List ℕ) (k : Fin (counts (j+1)+1)) :
    Measurable (fun s : PhysicalSample counts J n D => physicalFamily hdim hT s j I (basis k)) := by
  classical
  by_cases hj : j=J
  · subst j
    simp only [physicalFamily,dif_pos rfl,canonicalTerminalFrame,terminalBaseFrame,
      LinearIsometry.comp_apply,LinearIsometryEquiv.coe_toLinearIsometry]
    change Measurable (fun s : PhysicalSample counts J n D => orientation s.1 (n+1) •
      blockFrame counts (J+1) D (canonicalList counts (J+1) I)
        (canonicalList_length counts (J+1) I) (canonical_legalFrom counts (J+1) I) hT (basis k))
    exact ((orientation_continuous (n+1) D (n+1)).measurable.comp measurable_fst).smul measurable_const
  · simp only [physicalFamily,dif_neg hj]
    exact (canonicalFamily_column_measurable hdim j I k).comp
      (auxiliaryOrientations_measurable counts J n D)

theorem physicalFamily_endpoint_column {counts : ℕ → ℕ} {J n D : ℕ}
    (hdim : ∀ j,counts (j+1)+1≤D) (hT : capacity counts (J+1) 0≤D)
    (s : PhysicalSample counts J n D) (I : List ℕ) (v : EndpointTransportMatrix.Index n)
    (k : Fin (counts (J+1)+1)) :
    physicalRotations s.1 v (physicalFamily hdim hT s J I (basis k))=
      TransportNetwork.frame (capacity counts (J+1) 0) hT s.1 v (canonicalTerminalIndex counts (J+1) I k) := by
  rw [physicalFamily_terminal,canonical_terminal_network_column]

end Bilevel.TransportHierarchy

