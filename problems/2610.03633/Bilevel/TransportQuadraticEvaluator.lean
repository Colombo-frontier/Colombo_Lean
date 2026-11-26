import Bilevel.TransportQuadraticQuery
import Bilevel.TransportQuadraticSourceColumns
import Bilevel.EndpointTransportPrefixReply

/-! One fixed public evaluator for the complete original quadratic SFO
pair. The template sample is public; all hidden dependence is supplied by
the literal old prefix arrays and the single current frozen edge batch. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre
set_option autoImplicit false
set_option maxHeartbeats 1200000

def templateSample (counts : ℕ → ℕ) (J n D : ℕ) : PhysicalSample counts J n D :=
  ((1,fun _ => 1),fun _ => 1)

variable (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R δ c : ℝ)

def quadraticEvaluate (t : ℕ)
    (z : TransportProgram.Input (QuadraticQuery n D) (n+1) D 1
      (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
      (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) t) : QuadraticReply n D :=
  let counts := sourceCounts macroN cn ratios resolutions
  let s := templateSample counts 0 n D
  let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s initial Km
  let G := sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
  let data := quadraticSourceData macroN n D 1 t cn ratios resolutions z.2.1 z.2.2.1
  prefixQuadraticJointReply (fun _ => LinearIsometryEquiv.refl ℝ (Block D)) M ν G ρ R
    (fun q => counter counts 1 q 0 []) (fun q i => canonicalCounter counts 0 q 0 [i.val]) δ c 0
    (((t/(n+1),data),z.1),(quadraticNetworkQueries z.1,z.2.2.2))

theorem quadraticEvaluate_measurable
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
    [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)] (t : ℕ) :
    Measurable (quadraticEvaluate macroN n D cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν ρ R δ c t) := by
  let Z := TransportProgram.Input (QuadraticQuery n D) (n+1) D 1
    (Fintype.card (FrameIndex (sourceCounts macroN cn ratios resolutions) 0))
    (auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0) t
  have hstore : Measurable (fun z : Z => z.2.1) := measurable_fst.comp measurable_snd
  have hg : Measurable (fun z : Z => z.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hb : Measurable (fun z : Z => z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hdata := (quadraticSourceData_measurable macroN n D 1 t cn ratios resolutions).comp (hstore.prodMk hg)
  exact (prefixQuadraticJointReply_measurable
    (fun _ => LinearIsometryEquiv.refl ℝ (Block D))
    (sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial Km) ν
    (sourcePhysicalGeometry macroN 0 n D cn ratios resolutions hdim hT
      (templateSample (sourceCounts macroN cn ratios resolutions) 0 n D) initial weight A Kminus ζ CR) ρ R
    (fun q => counter (sourceCounts macroN cn ratios resolutions) 1 q 0 [])
    (fun q i => canonicalCounter (sourceCounts macroN cn ratios resolutions) 0 q 0 [i.val]) δ c (0 : Fin 1)).comp
      ((measurable_const.prodMk hdata).prodMk measurable_fst |>.prodMk
        ((quadraticNetworkQueries_measurable.comp measurable_fst).prodMk hb))

end Bilevel.TransportHierarchy
