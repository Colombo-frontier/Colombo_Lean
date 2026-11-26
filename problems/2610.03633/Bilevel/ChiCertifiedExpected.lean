import Bilevel.ChiCanonicalQueryCertificate

/-! The literal original full-SFO expected-query theorem instantiated with
one uniform analytic source certificate. Both gradient replies, all observer
and disclosure steps, and infinite nontermination costs are retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiHierarchyExecution ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre BorelAdaptive
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}


variable (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)

def CanonicalQueryCertificate.reply (μ π : ℝ) :=
  sourceOriginalJoint macroN J dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
    (J+1) (1/128) v (by norm_num) (H.width_pos J []) H.fine_ge_one (2*J)
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
    sourceBranchBound sourceBranchBound_lt_one H.regular H.actual_branch_bound
    (sc.curvature/24) (rad 0) (R 0) ((normalCoefficient L J) • normalOnes (2*J)) μ L π

variable [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))] [BorelSpace (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))]
  [MeasurableSpace (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))] [BorelSpace (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]
  [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))))]
  [BorelSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))))]
  [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))] [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]

theorem CanonicalQueryCertificate.expected_queries
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
    {Private State : Type*} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) ((FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) × (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))) (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))) (initial : Private → State) (hinit : Measurable initial)
    (ρseed : Measure Private) [IsProbabilityMeasure ρseed]
    (haccuracy : ∀ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll
        sc weight 3 1 ζ CR Km (J+1) (sc.curvature/24) rad R J K)
          (seededStopped alg (H.reply μ π) initial (a,z)))
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)))≤ENNReal.ofReal ε) :
    ∃ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),ENNReal.ofReal ((capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/(512*π))≤
      ∫⁻ z,seededCalls alg (H.reply μ π) initial (a,z)
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)) := by
  exact sourceCanonical_expected_queries macroN J dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
    (1/128) v (by norm_num) (H.width_pos J []) H.fine_ge_one (2*J)
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
    hR (fun i => H.width_pos (i.val+1) []) sourceBranchBound sourceBranchBound_lt_one
    H.regular H.actual_branch_bound H.actual H.virtual
    (by omega) hl hw hr hη hη1 hweight hζ hCR hKm (by norm_num)
    μ L π (sc.curvature/24) (rad 0) (R 0) K ε ((normalCoefficient L J) • normalOnes (2*J))
    hπ hπ1 hε N r bobs hmax hb hb2 hd hprod henergy hbudget H.barrier alg initial hinit ρseed haccuracy

end Bilevel.ChiHierarchyHaar
