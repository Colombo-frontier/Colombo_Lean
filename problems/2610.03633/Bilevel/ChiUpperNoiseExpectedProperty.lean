import Bilevel.ChiUpperNoiseExpectedQueries
import Bilevel.ChiUpperNoisePublicWitness

/-! The direct source's actual expected-query property and public dimension
choice. Its remaining barrier input is the deterministic calibrated mean
objective certificate, not an information or transcript assumption. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiUpperNoise
  PartialLegendre BorelAdaptive ChiCurvatureSchedule

variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ) (K ε : ℝ)

def UpperNoiseBarrier : Prop :=
  ∀ (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim) (x : UpperNoiseOutput dim),
    (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km).coordinates x.fst (Fin.last macroN)<sc.width →
    8*ε≤sourceOriginalLoss macroN 0 dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
      1 (sc.curvature/24) rad R 0 K a x

def UpperNoiseExpectedProperty (μ L π : ℝ) (hπ1 : π≤1) : Prop :=
  ∀ [MeasurableSpace (UpperNoiseOutput dim)] [BorelSpace (UpperNoiseOutput dim)]
    [MeasurableSpace (UpperNoiseQuery dim)] [BorelSpace (UpperNoiseQuery dim)],
  ∀ {Private State : Type*} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (UpperNoiseQuery dim) (UpperNoiseQuery dim × UpperNoiseQuery dim) (UpperNoiseOutput dim))
    (initial : Private → State) (_hinit : Measurable initial) (ρseed : Measure Private) [IsProbabilityMeasure ρseed]
    (_haccuracy : ∀ a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim,
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (sourceOriginalLoss macroN 0 dim cn ratios resolutions hdim hAll
        sc weight 3 1 ζ CR Km 1 (sc.curvature/24) rad R 0 K)
          (seededStopped alg (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
            (sc.curvature/24) rad R (publicLower μ L) π) initial (a,z)))
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)))≤ENNReal.ofReal ε),
    ∃ a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim,
      ENNReal.ofReal ((capacity (sourceCounts macroN cn ratios resolutions) 1 0:ℕ)/(512*π))≤
      ∫⁻ z,seededCalls alg (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
        (sc.curvature/24) rad R (publicLower μ L) π) initial (a,z)
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1))

theorem upper_noise_expected_property
    (hl : 0<sc.curvature) (hw : 0<sc.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (μ L π : ℝ) (hπ : 0<π) (hπ1 : π≤1) (hε : 0<ε)
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
    (hbarrier : UpperNoiseBarrier macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R K ε) :
    UpperNoiseExpectedProperty macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R K ε μ L π hπ1 := by
  intro instMO instBO instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  exact sourceUpperNoise_expected_queries macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
    hl hw hr hη hη1 hweight hζ hCR hKm (sc.curvature/24) rad R (publicLower μ L)
    (ChiQuadratic.lower_contDiff _ _ 3).continuous K π ε hπ hπ1 hε N r bobs hmax hb hb2 hd hprod henergy hbudget
    hbarrier alg initial hinit ρseed haccuracy

end Bilevel.ChiHierarchyHaar
