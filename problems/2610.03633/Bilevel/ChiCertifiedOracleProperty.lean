import Bilevel.ChiCertifiedOracles

/-! A compact exact original-SFO certificate for the same response used
by the expected-query execution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension ChiExtensionCalibration PartialLegendre ChiUpper
variable {macroN J dim : ℕ} {cn : ℝ} {ratios resolutions : ℕ → ℝ}
  {hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim}
  {hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim}
  {sc : Scale} {weight : ℕ → ℝ} {ζ CR Km : ℝ} {hJ : 1≤J}
  {v : ℝ} {rad R : ℕ → ℝ} {L K ε : ℝ}


variable (H : CanonicalQueryCertificate macroN J dim cn ratios resolutions hdim hAll sc weight ζ CR Km hJ v rad R L K ε)


def CanonicalQueryCertificate.HasFullOracle (μ ρ B : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
    (P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))
      (Y:=Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) μ L L L ρ) : Prop :=
  ∀ [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]
  [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))]
  [SecondCountableTopology (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J)))],
    ∀ (σf σg : ℝ),
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
      ∀ z coin,(Of.sample z coin,Og.sample z coin)=H.reply μ (BernoulliOracle.probability B σg) a z coin

theorem CanonicalQueryCertificate.hasFullOracle (μ ρ B : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
    (P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))
      (Y:=Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))) μ L L L ρ)
    (hf : ∀ x y,P.f x y=hierarchyUpper (J+1)
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a sc weight 3 1 ζ CR)
      J rad R (2*J) (normalCoefficient L J) x.fst y)
    (hO : ChiPrimitive.HasConservativeOracle P (H.lower μ true a) (H.lower μ false a) B)
    : H.HasFullOracle μ ρ B a P := by
  intro instM instB instS σf σg
  exact H.full_oracles μ ρ B a P hf hO σf σg

end Bilevel.ChiHierarchyHaar
