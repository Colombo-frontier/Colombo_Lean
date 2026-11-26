import Bilevel.TransportPhysicalCompleteCore
import Bilevel.ChiSourcePhysicalFullUpper
import Bilevel.TransportPhysicalOriginal
import Bilevel.TransportHierarchyFullDisclosure
import Bilevel.EndpointTransportVirtualJointExact

/-! Named original physical scalar and full-SFO reply on the one sampled
network/auxiliary family. The lower scalar is the actual hybrid partial
conjugate; no prescribed support or virtual oracle is part of this definition. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre ChiExtension ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 400000

variable (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (m δ c₀ cend : ℝ)


variable (hl : 0 < initial.curvature) (hw : 0 < initial.width)
  (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
  (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)

include hl hw hr hη hη1 hweight hζ hCR hKm in
theorem physicalOriginalPotential_full
    (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hℓ : fine.ℓ=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).ell)
    (hβ : fine.β=(sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR J []).width) :
    physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample=
      statePhysicalExtension
        (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
          (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km)
        (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
          (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
        fine index radialIndex fineIndex ρ R dn
        (fun _ => macroN+1) (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1)
        (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1)
        (0,completeHierarchyData hdim hAll hT sample) := by
  let data := completeHierarchyData hdim hAll hT sample
  have he := physicalOriginalCore_complete macroN J n D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn
    hl hw hr hη hη1 hweight hζ hCR hKm sample hℓ hβ
  refine (congrArg (physicalExtension (U:=Blocks J (Block D)) (D:=D)) he).trans ?_
  exact statePhysicalExtension_reframe
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km)
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
    (physicalMacroFrame hAll sample) (physicalFamily hdim hT sample)
    fine index radialIndex fineIndex ρ R dn
    (fun _ => macroN+1) (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1)
    (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1) (0,data)

include hl hw hr hη hη1 hweight hζ hCR hKm in
theorem physicalOriginalUpper_full (hJ : 0<J)
    (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) :
    physicalOriginalUpper macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R b sample=
      statePhysicalUpper (J:=J)
        (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
          (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km) ν
        (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
          (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
        (ρ 0) (R 0) b
        (fun _ => macroN+1) (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1)
        (0,completeHierarchyData hdim hAll hT sample) := by
  let data := completeHierarchyData hdim hAll hT sample
  have hc := completeHierarchyData_columns hdim hAll hT sample
  have he := source_physical_upper_full_prefix macroN J n D cn ratios resolutions initial weight A Kminus ζ CR Km
    (physicalMacroFrame hAll sample) (physicalFamily hdim hT sample) (physicalRotations sample.1)
    ρ R data.1 data.2.1 data.2.2.2 hc.1 hc.2.1 hc.2.2.2
    hl hw hr hη hη1 hweight hζ hCR hKm ν hJ
  refine (congrArg (fun f : PhysicalBase (Block D) J n D → ℝ =>
    physicalUpper (U:=Blocks J (Block D)) (D:=D) f b) he).trans ?_
  exact statePhysicalUpper_reframe
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km)
    (physicalMacroFrame hAll sample) ν
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
    (physicalFamily hdim hT sample) (ρ 0) (R 0) b
    (fun _ => macroN+1) (fun _ j _ => sourceChainIndex cn (ratios j) (resolutions j)+1) (0,data)

end Bilevel.TransportHierarchy
