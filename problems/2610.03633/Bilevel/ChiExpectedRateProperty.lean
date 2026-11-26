import Bilevel.ChiCertifiedDimension


/-! A fixed public dimension covers every truncation in the expected-time
argument, before any algorithm or orientation is chosen. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
universe u v
open ChiHierarchyIndex ChiTreeProgress ChiHierarchyExecution ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre BorelAdaptive ChiCurvatureSchedule
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}


variable (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)

def CanonicalQueryCertificate.RateProperty (μ π : ℝ) (hπ1 : π≤1) (rate : ℝ) : Prop :=
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
    ∃ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),ENNReal.ofReal rate≤
      ∫⁻ z,seededCalls alg (H.reply μ π) initial (a,z)
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1))

theorem CanonicalQueryCertificate.ExpectedProperty.rate {μ π rate : ℝ} {hπ1 : π≤1}
    (h : CanonicalQueryCertificate.ExpectedProperty.{u,v} H μ π hπ1)
    (hrate : rate≤(capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/(512*π)) :
    CanonicalQueryCertificate.RateProperty.{u,v} H μ π hπ1 rate := by
  intro instMX instBX instMY instBY instMR instBR instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  obtain ⟨a,ha⟩ := @h instMX instBX instMY instBY instMR instBR instMQ instBQ
    Private State instP instS alg initial hinit ρseed instρ haccuracy
  exact ⟨a,(ENNReal.ofReal_le_ofReal hrate).trans ha⟩

end Bilevel.ChiHierarchyHaar
