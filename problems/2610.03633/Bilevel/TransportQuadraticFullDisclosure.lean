import Bilevel.TransportQuadraticOriginal

/-! Complete physical frame arrays, used only to prove Borel dependence
of the ORIGINAL instance family. These arrays are not supplied to the
adaptive controller, which continues to use its literal prefix stores. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre ChiCarrier
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)

def completeQuadraticData (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D) :
    (Fin (macroN+1) → EuclideanGaussian.Space D) ×
      ((Fin (macroN+1) → Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1) → Physical n D) ×
       (Fin (macroN+1) → Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1) → Physical n D)) :=
  (fun k => physicalMacroFrame hAll s (basis k),
    (fun i k => insertion (n+2) 0
      (TransportNetwork.frame (capacity (sourceCounts macroN cn ratios resolutions) 1 0) hT s.1 0
        (canonicalTerminalIndex (sourceCounts macroN cn ratios resolutions) 1 [i.val] k)),
     fun i k => insertion (n+2) (Fin.last (n+1))
      (TransportNetwork.frame (capacity (sourceCounts macroN cn ratios resolutions) 1 0) hT s.1 (Fin.last (n+1))
        (canonicalTerminalIndex (sourceCounts macroN cn ratios resolutions) 1 [i.val] k))))

theorem completeQuadraticData_measurable
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] :
    Measurable (completeQuadraticData macroN n D cn ratios resolutions hAll hT) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro k
    exact physicalMacroFrame_column_measurable hAll k
  · apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro i <;>
      apply measurable_pi_lambda <;> intro k
    · exact (insertion (n+2) 0).continuous.measurable.comp
        ((measurable_pi_apply (canonicalTerminalIndex (sourceCounts macroN cn ratios resolutions) 1 [i.val] k)).comp
          ((measurable_pi_apply 0).comp
            ((TransportNetwork.frame_measurable (n+1) D _ hT).comp measurable_fst)))
    · exact (insertion (n+2) (Fin.last (n+1))).continuous.measurable.comp
        ((measurable_pi_apply (canonicalTerminalIndex (sourceCounts macroN cn ratios resolutions) 1 [i.val] k)).comp
          ((measurable_pi_apply (Fin.last (n+1))).comp
            ((TransportNetwork.frame_measurable (n+1) D _ hT).comp measurable_fst)))

theorem completeQuadraticData_source
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
    (i : Fin (macroN+1)) (k : Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1)) :
    (completeQuadraticData macroN n D cn ratios resolutions hAll hT s).2.1 i k=
      endpointFrame (physicalRotations s.1)
        (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR 0 [i.val]).frame
        0 (basis k) := by
  change insertion (n+2) 0 _=insertion (n+2) 0 _
  congr 1
  exact (physicalFamily_endpoint_column hdim hT s [i.val] 0 k).symm

theorem completeQuadraticData_target
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
    (i : Fin (macroN+1)) (k : Fin (sourceChainIndex cn (ratios 0) (resolutions 0)+1)) :
    (completeQuadraticData macroN n D cn ratios resolutions hAll hT s).2.2 i k=
      endpointFrame (physicalRotations s.1)
        (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR 0 [i.val]).frame
        (Fin.last (n+1)) (basis k) := by
  change insertion (n+2) (Fin.last (n+1)) _=insertion (n+2) (Fin.last (n+1)) _
  congr 1
  exact (physicalFamily_endpoint_column hdim hT s [i.val] (Fin.last (n+1)) k).symm

end Bilevel.TransportHierarchy
