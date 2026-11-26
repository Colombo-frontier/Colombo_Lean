import Bilevel.TransportHierarchyStoreData
import Bilevel.EndpointTransportHierarchyFullDisclosure

/-! Complete physical hierarchy arrays are a Borel function of the instance
sample. They represent the ORIGINAL scalar family only; the controller keeps
using the observable old/next prefix stores and never receives these arrays. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiCarrier ChiHierarchyHaar TransportRound
  TransportNetwork EndpointTransportResponse
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {counts : ℕ → ℕ} {J n D : ℕ}
  (hdim : ∀ j,counts (j+1)+1≤D) (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
  (hT : capacity counts (J+1) 0≤D)

def completeEndpointColumns (net : Latent (n+1) D) (v : EndpointTransportMatrix.Index n)
    (j : ℕ) (I : List ℕ) : Fin (counts (j+1)+1) → Physical n D :=
  if hj : j=J then by
    subst j
    exact fun k => insertion (n+2) v (TransportNetwork.frame (capacity counts (J+1) 0) hT net v
      (canonicalTerminalIndex counts (J+1) I k))
  else 0

def completeHierarchyData (sample : PhysicalSample counts J n D) : HierarchyStoreData counts n D :=
  (fun k => physicalMacroFrame hAll sample (basis k),
    (fun j I k => physicalFamily hdim hT sample j I (basis k),
      (completeEndpointColumns hT sample.1 0,completeEndpointColumns hT sample.1 (Fin.last (n+1)))))

theorem completeEndpointColumns_measurable
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] (v : EndpointTransportMatrix.Index n) :
    Measurable (fun sample : PhysicalSample counts J n D => completeEndpointColumns hT sample.1 v) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro I
  by_cases hj : j=J
  · subst j
    simp only [completeEndpointColumns,dif_pos rfl]
    apply measurable_pi_lambda
    intro k
    exact (insertion (n+2) v).continuous.measurable.comp
      ((measurable_pi_apply (canonicalTerminalIndex counts (J+1) I k)).comp
        ((measurable_pi_apply v).comp ((TransportNetwork.frame_measurable (n+1) D _ hT).comp measurable_fst)))
  · simp only [completeEndpointColumns,dif_neg hj]
    exact measurable_const

theorem completeHierarchyData_measurable
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] :
    Measurable (completeHierarchyData (n:=n) hdim hAll hT) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro k
    exact physicalMacroFrame_column_measurable hAll k
  · apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro j
      apply measurable_pi_lambda
      intro I
      apply measurable_pi_lambda
      intro k
      exact physicalFamily_column_measurable hdim hT j I k
    · exact (completeEndpointColumns_measurable hT 0).prodMk
        (completeEndpointColumns_measurable hT (Fin.last (n+1)))

theorem completeEndpointColumns_eq (sample : PhysicalSample counts J n D)
    (v : EndpointTransportMatrix.Index n) (I : List ℕ) (k : Fin (counts (J+1)+1)) :
    completeEndpointColumns hT sample.1 v J I k=
      endpointFrame (physicalRotations sample.1) (physicalFamily hdim hT sample J I) v (basis k) := by
  simp only [completeEndpointColumns,dif_pos rfl]
  change insertion (n+2) v _=insertion (n+2) v _
  congr 1
  exact (physicalFamily_endpoint_column hdim hT sample I v k).symm

theorem completeHierarchyData_columns (sample : PhysicalSample counts J n D) :
    (∀ k,(completeHierarchyData hdim hAll hT sample).1 k=physicalMacroFrame hAll sample (basis k)) ∧
    (∀ j I k,(completeHierarchyData hdim hAll hT sample).2.1 j I k=physicalFamily hdim hT sample j I (basis k)) ∧
    (∀ I k,(completeHierarchyData hdim hAll hT sample).2.2.1 J I k=
      endpointFrame (physicalRotations sample.1) (physicalFamily hdim hT sample J I) 0 (basis k)) ∧
    (∀ I k,(completeHierarchyData hdim hAll hT sample).2.2.2 J I k=
      endpointFrame (physicalRotations sample.1) (physicalFamily hdim hT sample J I) (Fin.last (n+1)) (basis k)) := by
  exact ⟨fun _ => rfl,fun _ _ _ => rfl,completeEndpointColumns_eq hdim hT sample 0,
    completeEndpointColumns_eq hdim hT sample (Fin.last (n+1))⟩

end Bilevel.TransportHierarchy
