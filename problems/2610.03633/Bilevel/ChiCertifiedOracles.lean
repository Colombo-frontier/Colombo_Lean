import Bilevel.ChiCertifiedExpected
import Bilevel.ChiJointConservativeOracle

/-! Exact identification of the certified execution reply with a pair of
actual original SFOs for the same Primitive. The nonlinear upper gradient
is retained and the inactive conjugate uses its distinct 1/4 certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
namespace Bilevel.ChiUpper
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace X] [CompleteSpace U] in
theorem fullUpper_contDiff (f : Joint X U → ℝ) (hf : ContDiff ℝ 3 f) (b : V) :
    ContDiff ℝ 3 (fullUpper f b) := by
  let R : FullNormalVariables X U V →L[ℝ] V := jointSndLinear.comp jointSndLinear
  have ha := hf.comp (baseProjection : FullNormalVariables X U V →L[ℝ] Joint X U).contDiff
  have hb := ((InnerProductSpace.toDual ℝ V b).comp R).contDiff (n:=3)
  exact ha.add hb

end Bilevel.ChiUpper

namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre ChiUpper
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}


variable (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)


def CanonicalQueryCertificate.lower (μ : ℝ) (active : Bool)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) :=
  sourceOriginalLower macroN J dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
    (J+1) (1/128) v (by norm_num) (H.width_pos J []) H.fine_ge_one (2*J)
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
    sourceBranchBound sourceBranchBound_lt_one H.regular H.actual_branch_bound μ L active a

variable [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]
  [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]
  [SecondCountableTopology (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]

theorem CanonicalQueryCertificate.full_oracles (μ ρ B : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
    (P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))
      (Y:=Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) μ L L L ρ)
    (hf : ∀ x y,P.f x y=hierarchyUpper (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
      J rad R (2*J) (normalCoefficient L J) x.fst y)
    (hO : ChiPrimitive.HasConservativeOracle P (H.lower μ true a) (H.lower μ false a) B)
    (σf σg : ℝ) :
    ∃ hB : 0<B,
    ∃ Of : FreshOracle.Oracle
      (Query:=FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))
      (E:=FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))
      (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) σf,
    ∃ Og : FreshOracle.Oracle
      (Query:=FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))
      (E:=FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))
      (BernoulliOracle.law (BernoulliOracle.probability B σg) (BernoulliOracle.probability_le_one hB)) σg,
      (∀ z,Of.truth z=pack (P.fx z.fst z.snd) (P.fy z.fst z.snd)) ∧
      (∀ z,Og.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
      ∀ z coin,(Of.sample z coin,Og.sample z coin)=H.reply μ (BernoulliOracle.probability B σg) a z coin := by
  let f := fullUpper (upperBase (J+1)
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
    J (rad 0) (R 0)) ((normalCoefficient L J) • normalOnes (2*J))
  have hfc : ContDiff ℝ 3 f := fullUpper_contDiff _ (upperBase_contDiff _ _ _ _ _ _ _) _
  have hPf : ∀ x y,P.f x y=f (pack x y) := by
    intro x y
    rw [hf]
    dsimp only [f,fullUpper,hierarchyUpper]
    rw [real_inner_smul_left,← InnerProductSpace.toDual_apply,normalOnes_toDual]
    rfl
  have hg (active : Bool) : Differentiable ℝ (H.lower μ active a) := by
    intro z
    exact (fullExtensionLower_hasGradientAt _ (H.regular active a) (sourceBranchBound active)
      (H.actual_branch_bound active a) (sourceBranchBound_lt_one active) μ L z).differentiableAt
  exact ChiPrimitive.full_joint_oracles_of_conservative P f (H.lower μ true a) (H.lower μ false a)
    hfc (hg true) (hg false) hPf hO σf σg

end Bilevel.ChiHierarchyHaar
