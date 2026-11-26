import Bilevel.TransportPhysicalEvaluator
import Bilevel.EndpointTransportVirtualJointFrame
import Bilevel.TransportHierarchySourceReframe
import Bilevel.TransportQuadraticEvaluator
import Bilevel.TransportHierarchyStoreData
import Bilevel.EndpointTransportVirtualUpperBorel

/-! A fixed public full-SFO evaluator for the positive-depth physical
hierarchy. Only the old auxiliary/network stores and one frozen edge batch
enter the evaluator; no sampled hidden frame is an input. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
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


theorem physicalEvaluate_template_independent
    (sample : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D) (t : ℕ)
    (z : TransportProgram.Input (PhysicalQuery J n D s) (n+1) D 1
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J) t) :
    physicalEvaluate macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend t z=
      physicalPrefixJointReply (n:=n)
        (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km) ν
        (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR)
        fine index radialIndex fineIndex ρ R dn b
        (fun q => counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 [])
        (fun q => canonicalCounter (sourceCounts macroN cn ratios resolutions) J q)
        (fun q => canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q+1)) m δ c₀ cend 0
        (((t/(n+1),hierarchyStoreData (sourceCounts macroN cn ratios resolutions) J 1 t z.2.1 z.2.2.1),z.1),
          (physicalNetworkQueries z.1,z.2.2.2)) := by
  dsimp only [physicalEvaluate]
  have h := physicalPrefixJointReply_reframe
    (n:=n) (a:=size (n+1) 1 1 1 t)
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km)
    (physicalMacroFrame hAll sample) ν
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
    (physicalFamily hdim hT sample) fine index radialIndex fineIndex ρ R dn b
    (fun q => counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 [])
    (fun q => canonicalCounter (sourceCounts macroN cn ratios resolutions) J q)
    (fun q => canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q+1)) m δ c₀ cend (0 : Fin 1)
  exact (congrFun h
    (((t/(n+1),hierarchyStoreData (sourceCounts macroN cn ratios resolutions) J 1 t z.2.1 z.2.2.1),z.1),
      (physicalNetworkQueries z.1,z.2.2.2))).symm

end Bilevel.TransportHierarchy
