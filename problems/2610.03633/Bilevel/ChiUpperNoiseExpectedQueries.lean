import Bilevel.ChiUpperNoiseCanonicalReply
import Bilevel.ChiUpperNoiseDimension
import Bilevel.ChiSourceExpectedQueries
import Bilevel.ChiSourcePointwiseReply

/-! Actual expected original-call lower bound for the canonical J=0
upper-noise source. Oracle equality and all event probabilities are proved
from the same finite Haar execution, not assumed as query certificates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiUpperNoise
  PartialLegendre BorelAdaptive

abbrev UpperNoiseQuery (dim : ℕ) := Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim))
abbrev UpperNoiseOutput (dim : ℕ) := Joint (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim))

variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)
  [MeasurableSpace (UpperNoiseOutput dim)] [BorelSpace (UpperNoiseOutput dim)]
  [MeasurableSpace (UpperNoiseQuery dim)] [BorelSpace (UpperNoiseQuery dim)]

theorem sourceUpperNoise_expected_queries
    (hl : 0<sc.curvature) (hw : 0<sc.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (ν : ℝ) (ρ R : ℕ → ℝ) (g : UpperNoiseQuery dim → ℝ) (hg : Continuous g)
    (K π ε : ℝ) (hπ : 0<π) (hπ1 : π≤1) (hε : 0<ε)
    (N r : ℕ) (bobs : ℝ)
    (hmax : (capacity (sourceCounts macroN cn ratios resolutions) 1 0:ℕ)/(16*π)≤(N:ℝ))
    (hb : 0<bobs) (hb2 : bobs≤2)
    (hd : (2*(N*batchSize (sourceCounts macroN cn ratios resolutions) 0 (queryVectorCount 1))+1)+
      (N*batchSize (sourceCounts macroN cn ratios resolutions) 0 (queryVectorCount 1))+(r+1)≤dim)
    (hprod : ((N*batchSize (sourceCounts macroN cn ratios resolutions) 0 (queryVectorCount 1):ℕ):ℝ)*
      (((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) 0 (queryVectorCount 1))+1:ℕ):ℝ)*bobs)≤1/2)
    (henergy : 2*((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) 0 (queryVectorCount 1))+1:ℕ):ℝ)*bobs≤
      sourcePublicCap macroN 0 sc ratios resolutions weight CR ζ Km (sourcePublicWidth sc ratios resolutions 0/2))
    (hbudget : ((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) 0 (queryVectorCount 1))+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns (sourceCounts macroN cn ratios resolutions) 0) r bobs≤1/8)
    (hbarrier : ∀ (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim) (x : UpperNoiseOutput dim),
      (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km).coordinates x.fst (Fin.last macroN)<sc.width →
      8*ε≤sourceOriginalLoss macroN 0 dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km 1 ν ρ R 0 K a x)
    {Private State : Type*} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (UpperNoiseQuery dim) (UpperNoiseQuery dim × UpperNoiseQuery dim) (UpperNoiseOutput dim))
    (initial : Private → State) (hinit : Measurable initial) (ρseed : Measure Private) [IsProbabilityMeasure ρseed]
    (haccuracy : ∀ a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim,
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (sourceOriginalLoss macroN 0 dim cn ratios resolutions hdim hAll
        sc weight A Kminus ζ CR Km 1 ν ρ R 0 K)
          (seededStopped alg (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
            ν ρ R g π) initial (a,z)))
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)))≤ENNReal.ofReal ε) :
    ∃ a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim,
      ENNReal.ofReal ((capacity (sourceCounts macroN cn ratios resolutions) 1 0:ℕ)/(512*π))≤
      ∫⁻ z,seededCalls alg (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
        ν ρ R g π) initial (a,z) ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)) := by
  let M := sourceTemplateMacro macroN 0 dim cn ratios resolutions hAll sc Km
  let D := sourceTemplateGeometry macroN 0 dim cn ratios resolutions hdim sc weight A Kminus ζ CR
  let counts := sourceCounts macroN cn ratios resolutions
  let cap := sourcePublicCap macroN 0 sc ratios resolutions weight CR ζ Km (sourcePublicWidth sc ratios resolutions 0/2)
  let evaluate := finiteDirectEvaluate counts 1 M ν D rfl (fun _ _ => rfl) ρ R g π
  have he := finiteDirectEvaluate_measurable counts 1 M ν D rfl (fun _ _ => rfl) ρ R g hg π
  let original := sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km ν ρ R g π
  have hOrig := sourceUpperNoiseJoint_measurable macroN dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km ν ρ R g hg π
  have geo := sourceCanonical_geometry macroN 0 dim cn ratios resolutions hdim hAll (fun _ => 1) sc weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have hτ : 0<sourcePublicWidth sc ratios resolutions 0/2 :=
    div_pos (geo.2.2.1 0 []).1 (by norm_num)
  have hcap := sourceCanonical_cap_certificate macroN 0 dim cn ratios resolutions hdim hAll (fun _ => 1)
    sc weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm (sourcePublicWidth sc ratios resolutions 0/2) hτ
  rw [sourceCanonical_cap_eq_public] at hcap
  let point : UpperNoiseOutput dim → EuclideanGaussian.Space dim := fun x => x.fst
  have hpoint : Measurable point := (jointFstLinear : UpperNoiseOutput dim →L[ℝ] EuclideanGaussian.Space dim).continuous.measurable
  have hreply (a : Orientations counts 0 dim) (q : ℕ) (p : UpperNoiseQuery dim) (coin : Bool)
      (hE : ∀ i : FrameIndex counts 0,GenieProtocol.BoundedEnergy
        (sharedKnown counts 0 dim q (columns hAll a) (Submodule.span ℝ (Set.range (upperNoiseVectors p))))
        (prefixSet (retained counts 0 q i)) (columns hAll a i) cap) :
      original a p coin=evaluate p (actual counts 0 q (columns hAll a))
        (actual counts 0 (q+if coin then 1 else 0) (columns hAll a)) coin := by
    exact (sourceCanonical_upperNoise_template_reply_from_energy macroN dim cn ratios resolutions hdim hAll a sc weight
      A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm q p hE (fun _ => 1) ν ρ R g π coin).symm
  refine expected_queries_of_source_replies counts 0 dim (queryVectorCount 1) hAll alg evaluate he
    (fun k p => upperNoiseVectors p.1 k) (fun k => (upperNoiseVectors_measurable k).comp measurable_fst)
    M.radius sc.width cap geo.2.1 hw hcap.1.le hcap.2.2.1 point hpoint initial hinit original hOrig
    (Function.uncurry (sourceOriginalLoss macroN 0 dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km 1 ν ρ R 0 K))
    (sourceOriginalLoss_measurable macroN 0 dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km 1 ν ρ R 0 K)
    (fun _ => norm_nonneg _) ρseed π ε hπ hπ1 hε N r bobs hmax hb hb2 hd hprod henergy hbudget
    ?_ (fun a x hx => hbarrier a x hx) haccuracy
  intro n _ z hgood t ht _ _
  exact sourceGood_reply_from_energy hAll alg evaluate he
    (fun k p => upperNoiseVectors p k) (fun k => upperNoiseVectors_measurable k)
    (macroTerminal M.radius point) (macroTerminal_measurable M.radius point hpoint)
    initial original cap hreply n z hgood t ht

end Bilevel.ChiHierarchyHaar
