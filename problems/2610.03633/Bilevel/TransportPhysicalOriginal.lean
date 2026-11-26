import Bilevel.TransportPhysicalTemplate
import Bilevel.EndpointTransportVirtualJointExact

/-! Named original physical scalar and full-SFO reply on the one sampled
network/auxiliary family. The lower scalar is the actual hybrid partial
conjugate; no prescribed support or virtual oracle is part of this definition. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (m δ c₀ cend : ℝ)

def physicalOriginalCore (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) :
    Full (PhysicalBase (Block D) J n D) s → ℝ :=
  physicalHierarchyExtension (physicalRotations sample.1)
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km)
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR)
    fine J s index radialIndex fineIndex ρ R dn

def physicalOriginalPotential (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) :
    PhysicalQuery J n D s → ℝ :=
  physicalExtension (physicalOriginalCore macroN J n D s cn ratios resolutions hdim hAll hT
    initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)

def physicalOriginalUpper (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) :
    PhysicalQuery J n D s → ℝ :=
  physicalUpper
    (physicalUpperBase J (physicalRotations sample.1)
      (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km) ν
      (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR)
      J (ρ 0) (R 0)) b

variable (K : NNReal) (hK : K<1)
  (hF : ∀ sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D,
    LipschitzWith K (gradient (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)))

def physicalOriginalLower (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) :
    PhysicalQuery J n D s → ℝ :=
  hybridLower (hF sample) hK
    (physicalOriginalPotential macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn sample)
    m (ChiHybrid.correction (hybridHessian m δ (physicalRotations sample.1)) m)
    (hybridCoupling c₀ cend (physicalRotations sample.1))

def physicalOriginalReply (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (w : PhysicalQuery J n D s) : PhysicalReply J n D s :=
  (gradient (physicalOriginalUpper macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km ν ρ R b sample) w,
    gradient (physicalOriginalLower macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km fine index radialIndex fineIndex ρ R dn m δ c₀ cend K hK hF sample) w)

end Bilevel.TransportHierarchy
