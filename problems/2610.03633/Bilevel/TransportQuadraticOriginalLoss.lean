import Bilevel.TransportQuadraticLoss
import Bilevel.EndpointTransportOneBlockCoordinates

/-! The original physical mean-gradient loss in the algorithm's actual
two-block outer output space. The isometric regrouping loses no factor. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse PrimitiveGeometry ChiCarrier ChiOuter
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (ρ R : ℕ → ℝ) (K : ℝ)

def quadraticOriginalLoss (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (x : QuadraticOutput D) : ℝ :=
  ‖gradient (jointOuter 1
    (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km) ν
    (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR)
    ρ R 0 K) (oneBlockCoordinates x)‖

theorem quadraticOriginalLoss_nonneg (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (x : QuadraticOutput D) :
    0≤quadraticOriginalLoss macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K s x :=
  norm_nonneg _

theorem quadraticOriginalLoss_measurable
    [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)] :
    Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticOutput D =>
      quadraticOriginalLoss macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R K p.1 p.2) := by
  letI : MeasurableSpace (Joint (Block D) (Blocks 1 (Block D))) := borel _
  letI : BorelSpace (Joint (Block D) (Blocks 1 (Block D))) := ⟨rfl⟩
  have hm : Measurable (fun p : PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D × QuadraticOutput D =>
      (p.1,oneBlockCoordinates p.2)) :=
    measurable_fst.prodMk ((oneBlockCoordinates (E:=Block D) (F:=Block D)).continuous.measurable.comp measurable_snd)
  have h := (sourcePhysical_mean_loss_measurable macroN 0 n D cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km 1 ν ρ R 0 K).comp hm
  simpa only [quadraticOriginalLoss] using h

end Bilevel.TransportHierarchy
