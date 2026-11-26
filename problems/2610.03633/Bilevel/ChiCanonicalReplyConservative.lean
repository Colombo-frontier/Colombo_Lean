import Bilevel.ChiCertifiedOracleProperty

/-! Every literal original reply of the canonical family is the gradient of
two globally defined scalar samples. This is stronger than moment bounds. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre ChiUpper
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}
  (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)

theorem CanonicalQueryCertificate.reply_conservative (μ π : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) (coin : Bool) :
    ∃ f g : FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)) → ℝ,
      (∀ q,HasGradientAt f (H.reply μ π a q coin).1 q) ∧
      (∀ q,HasGradientAt g (H.reply μ π a q coin).2 q) := by
  let f := fullUpper (upperBase (J+1)
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
    J (rad 0) (R 0)) ((normalCoefficient L J) • normalOnes (2*J))
  have hf : ContDiff ℝ 3 f := fullUpper_contDiff _ (upperBase_contDiff _ _ _ _ _ _ _) _
  have hg (active : Bool) : Differentiable ℝ (H.lower μ active a) := by
    intro z
    exact (fullExtensionLower_hasGradientAt _ (H.regular active a) (sourceBranchBound active)
      (H.actual_branch_bound active a) (sourceBranchBound_lt_one active) μ L z).differentiableAt
  refine ⟨f,ChiConservative.samplePotential (H.lower μ true a) (H.lower μ false a) π coin,?_,?_⟩
  · intro q
    exact (hf.differentiable (by norm_num) q).hasGradientAt
  · intro q
    exact ChiConservative.sample_hasGradientAt _ _ (hg true) (hg false) π coin q

end Bilevel.ChiHierarchyHaar
