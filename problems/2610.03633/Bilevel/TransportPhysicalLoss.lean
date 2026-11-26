import Bilevel.TransportQuadraticLoss
import Bilevel.TransportPhysicalQuery
import Bilevel.EndpointTransportHybridGradient

/-! Joint Borel dependence of the actual physical mean-gradient loss.
The isometric coordinate regrouping preserves the entire gradient norm. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse PrimitiveGeometry ChiOuter
set_option autoImplicit false
set_option maxHeartbeats 1100000

variable (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (ρ R : ℕ → ℝ) (K : ℝ)

def physicalOriginalMean (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (x : PhysicalOutput J D) : ℝ :=
  jointOuter (J+1)
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km) ν
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR)
    ρ R J K (sourceCoordinates J D x)

def physicalOriginalLoss (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (x : PhysicalOutput J D) : ℝ :=
  ‖gradient (physicalOriginalMean macroN J n D cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν ρ R K sample) x‖

theorem physicalOriginalLoss_eq_source
    (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) (x : PhysicalOutput J D) :
    physicalOriginalLoss macroN J n D cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km ν ρ R K sample x=
      ‖gradient (jointOuter (J+1)
        (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km) ν
        (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR)
        ρ R J K) (sourceCoordinates J D x)‖ := by
  have hd := (jointOuter_contDiff (J+1)
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km) ν
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR)
    ρ R J K 1).differentiable (by norm_num)
  have hh := gradient_norm_comp_isometryEquiv (sourceCoordinatesEquiv (E:=Block D) J D)
    (jointOuter (J+1)
      (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km) ν
      (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR)
      ρ R J K) x (hd _)
  simpa only [physicalOriginalLoss,physicalOriginalMean,sourceCoordinatesEquiv,LinearIsometryEquiv.coe_ofSurjective] using hh

theorem physicalOriginalLoss_measurable
    [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)] :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalOutput J D =>
      physicalOriginalLoss macroN J n D cn ratios resolutions hdim hAll hT
        initial weight A Kminus ζ CR Km ν ρ R K p.1 p.2) := by
  let Y := Joint (Block D) (Blocks (J+1) (Block D))
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  let Z := PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D × PhysicalOutput J D
  have hx : Measurable (fun p : Z => sourceCoordinates (E:=Block D) J D p.2) :=
    (sourceCoordinates (E:=Block D) J D).continuous.measurable.comp measurable_snd
  have hh := (sourcePhysical_mean_loss_measurable macroN J n D cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km (J+1) ν ρ R J K).comp (measurable_fst.prodMk hx)
  convert hh using 1
  funext p
  exact physicalOriginalLoss_eq_source macroN J n D cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km ν ρ R K p.1 p.2

end Bilevel.TransportHierarchy
