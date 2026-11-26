import Bilevel.TransportPhysicalQuery
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

def physicalEvaluate (t : ℕ)
    (z : TransportProgram.Input (PhysicalQuery J n D s) (n+1) D 1
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J) t) : PhysicalReply J n D s :=
  let counts := sourceCounts macroN cn ratios resolutions
  let sample := templateSample counts J n D
  let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll sample initial Km
  let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT sample initial weight A Kminus ζ CR
  let data := hierarchyStoreData counts J 1 t z.2.1 z.2.2.1
  physicalPrefixJointReply (n:=n) M ν G fine index radialIndex fineIndex ρ R dn b
    (fun q => counter counts (J+1) q 0 [])
    (fun q => canonicalCounter counts J q)
    (fun q => canonicalCounter counts J (q+1)) m δ c₀ cend 0
    (((t/(n+1),data),z.1),(physicalNetworkQueries z.1,z.2.2.2))

theorem physicalEvaluate_measurable
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)] (t : ℕ) :
    Measurable (physicalEvaluate macroN J n D s cn ratios resolutions hdim hAll hT
      initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend t) := by
  let Z := TransportProgram.Input (PhysicalQuery J n D s) (n+1) D 1
    (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) J))
    (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J) t
  have hstore : Measurable (fun z : Z => z.2.1) := measurable_fst.comp measurable_snd
  have hg : Measurable (fun z : Z => z.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hb : Measurable (fun z : Z => z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hdata := (hierarchyStoreData_measurable (sourceCounts macroN cn ratios resolutions) J 1 t).comp
    (hstore.prodMk hg)
  have hcount : Measurable (fun _ : Z => t/(n+1)) := measurable_const
  have he := (physicalPrefixJointReply_measurable (n:=n)
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial Km) ν
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) J n D) initial weight A Kminus ζ CR)
    fine index radialIndex fineIndex ρ R dn b
    (fun q => counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 [])
    (fun q => canonicalCounter (sourceCounts macroN cn ratios resolutions) J q)
    (fun q => canonicalCounter (sourceCounts macroN cn ratios resolutions) J (q+1)) m δ c₀ cend (0 : Fin 1)).comp
      ((hcount.prodMk hdata).prodMk measurable_fst |>.prodMk
        ((physicalNetworkQueries_measurable.comp measurable_fst).prodMk hb))
  exact he

end Bilevel.TransportHierarchy
