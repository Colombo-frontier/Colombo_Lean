import Bilevel.TransportQuadraticFullDisclosure
import Bilevel.ChiOriginalBorelMean

/-! The actual mean-gradient loss of the physical source is jointly
Borel in the fixed instance and arbitrary returned outer point. Complete
arrays are used only for this original-family representation. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse PrimitiveGeometry ChiCarrier ChiOuter ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

def sourcePhysicalCompleteData : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D →
    HierarchyData
      (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
        (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km)
      (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
        (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR) :=
  frameData _ _ (physicalMacroFrame hAll) (physicalFamily hdim hT)

theorem sourcePhysicalCompleteData_measurable :
    Measurable (sourcePhysicalCompleteData macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km) := by
  unfold sourcePhysicalCompleteData frameData
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro k
    exact physicalMacroFrame_column_measurable hAll k
  · apply measurable_pi_lambda
    intro j
    apply measurable_pi_lambda
    intro I
    apply measurable_pi_lambda
    intro k
    exact physicalFamily_column_measurable hdim hT j I k

theorem sourcePhysical_mean_loss_measurable (m : ℕ) (ν : ℝ) (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ)
    [MeasurableSpace (Joint (Block D) (Blocks m (Block D)))]
    [BorelSpace (Joint (Block D) (Blocks m (Block D)))] :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D ×
        Joint (Block D) (Blocks m (Block D)) =>
      ‖gradient (jointOuter m
        (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll p.1 initial Km) ν
        (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT p.1 initial weight A Kminus ζ CR)
        ρ R d K) p.2‖) := by
  exact original_mean_loss_measurable m
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km) ν
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
    ρ R d K (physicalMacroFrame hAll) (physicalFamily hdim hT)
    (sourcePhysicalCompleteData_measurable macroN J n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km)

end Bilevel.TransportHierarchy
