import Bilevel.ChiCertifiedExpected
import Bilevel.ChiSourceCalibratedDimension

/-! A fixed public dimension covers every truncation in the expected-time
argument, before any algorithm or orientation is chosen. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiHierarchyExecution ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre BorelAdaptive ChiCurvatureSchedule
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}


variable (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)

def CanonicalQueryCertificate.ExpectedProperty (μ π : ℝ) (hπ1 : π≤1) : Prop :=
  ∀ [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))] [BorelSpace (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))]
  [MeasurableSpace (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))] [BorelSpace (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]
  [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))))]
  [BorelSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))))]
  [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))] [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))],
    ∀ {Private State : Type*} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) ((FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) × (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))) (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))) (initial : Private → State) (_hinit : Measurable initial)
    (ρseed : Measure Private) [IsProbabilityMeasure ρseed]
    (_haccuracy : ∀ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll
        sc weight 3 1 ζ CR Km (J+1) (sc.curvature/24) rad R J K)
          (seededStopped alg (H.reply μ π) initial (a,z)))
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)))≤ENNReal.ofReal ε),
    ∃ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),ENNReal.ofReal ((capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/(512*π))≤
      ∫⁻ z,seededCalls alg (H.reply μ π) initial (a,z)
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1))

theorem CanonicalQueryCertificate.expected_property
    (hR : ∀ i : Fin J,0<R (i.val+1))
    (hl : 0<sc.curvature) (hw : 0<sc.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (μ π : ℝ) (hπ : 0<π) (hπ1 : π≤1) (hε : 0<ε)
    (N r : ℕ) (bobs : ℝ) (hmax : (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/(16*π)≤(N:ℝ))
    (hb : 0<bobs) (hb2 : bobs≤2)
    (hd : (2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1)+
      (N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+(r+1)≤dim)
    (hprod : ((N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)):ℕ):ℝ)*
      (((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1:ℕ):ℝ)*bobs)≤1/2)
    (henergy : 2*((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1:ℕ):ℝ)*bobs≤(sourcePublicCap macroN J sc ratios resolutions weight CR ζ Km (ZeroChainSchedule.width (1/128) ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight 3 1 ζ CR) J []).width v (ZeroChainSchedule.levels v))))
    (hbudget : ((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns (sourceCounts macroN cn ratios resolutions) J) r bobs≤1/8)
    : H.ExpectedProperty μ π hπ1 := by
  intro instMX instBX instMY instBY instMR instBR instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  exact H.expected_queries hR hl hw hr hη hη1 hweight hζ hCR hKm μ π hπ hπ1 hε
    N r bobs hmax hb hb2 hd hprod henergy hbudget alg initial hinit ρseed haccuracy

theorem exists_source_expected_dimension (macroN J : ℕ) (hJ : 1≤J)
    (sc : Scale) (cn T η Kg v μ L K ε π CR ζ Km : ℝ) (weight : ℕ → ℝ)
    (hl : 0<sc.curvature) (hw : 0<sc.width) (hcn : 0≤cn) (hT : 1≤T)
    (hη : 0<η) (hKg : 0<Kg) (hv : 1≤v)
    (hres : ∀ j,resolution η Kg j≤1) (hweight : ∀ j,0<weight j)
    (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) (hπ : 0<π) (hπ1 : π≤1) (hε : 0<ε) :
    ∃ dim : ℕ,
    ∃ hdim : ∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤dim,
    ∃ hAll : ∀ i : FrameIndex (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J,chainSize i+1≤dim,
    ∀ H : CanonicalQueryCertificate macroN J dim cn (sourceRatio T) (resolution η Kg) hdim hAll
      sc weight ζ CR Km hJ v (sourcePublicRadialWeight sc (sourceRatio T) (resolution η Kg) weight ζ)
      (sourcePublicNodeRadius sc (sourceRatio T) (resolution η Kg) weight CR ζ) L K ε,
    H.ExpectedProperty μ π hπ1 := by
  obtain ⟨hcap,dim,r,b,hD,hdim,hAll,hd,hr,hb,hb2,hprod,henergy,hprob⟩ :=
    exists_calibrated_source_dimension macroN J sc cn T η Kg (1/128) v π CR ζ Km weight
      hl hw hcn hT hη hKg (by norm_num) hv hweight hCR hζ hKm
  refine ⟨dim,hdim,hAll,?_⟩
  intro H
  exact H.expected_property
    (fun i => sourcePublicNodeRadius_pos sc (sourceRatio T) (resolution η Kg) weight CR ζ
      hl hw (sourceRatio_ge_one hT) (base_resolution_positive hη hKg) hweight hCR hζ (i.val+1))
    hl hw (sourceRatio_ge_one hT) (base_resolution_positive hη hKg) hres hweight hζ hCR hKm
    μ π hπ hπ1 hε (sourceHorizon (actualCounts macroN cn η T Kg) J π) r b
    (sourceHorizon_bound _ J π) hb hb2 hd hprod henergy hprob.le

end Bilevel.ChiHierarchyHaar
