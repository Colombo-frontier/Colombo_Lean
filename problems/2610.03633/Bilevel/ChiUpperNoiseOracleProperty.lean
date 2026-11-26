import Bilevel.ChiUpperNoiseCertifiedOracles

/-! The exact response used by the direct execution compiler is a complete
pair of original SFOs for the same retained Primitive, for arbitrary declared
upper and lower variance bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry ChiUpperNoise
variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ)

def HasUpperNoiseFullOracle (μ L ρg B : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim)
    (P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (Y:=Blocks 1 (EuclideanGaussian.Space dim)) μ L L L ρg)
 : Prop :=
  ∀ [MeasurableSpace (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))]
    [BorelSpace (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))]
    [SecondCountableTopology (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))],
    ∀ (σf σg : ℝ),
    ∃ hB : 0<B,
    ∃ Of : FreshOracle.Oracle
      (Query:=Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (E:=Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) σf,
    ∃ Og : FreshOracle.Oracle
      (Query:=Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (E:=Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (BernoulliOracle.law (BernoulliOracle.probability B σf) (BernoulliOracle.probability_le_one hB)) σg,
      (∀ z,Of.truth z=pack (P.fx z.fst z.snd) (P.fy z.fst z.snd)) ∧
      (∀ z,Og.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
      ∀ z coin,(Of.sample z coin,Og.sample z coin)=
        sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
          (sc.curvature/24) rad R (publicLower μ L) (BernoulliOracle.probability B σf) a z coin

theorem hasUpperNoiseFullOracle (μ L ρg B : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim)
    (P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (Y:=Blocks 1 (EuclideanGaussian.Space dim)) μ L L L ρg)
    (hO : HasUpperNoiseOracle P
      (fullCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
        (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight 3 1 ζ CR) rad R)
      (fullInactiveCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) (sc.curvature/24)
        (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight 3 1 ζ CR) rad R)
      (publicLower μ L) B) :
    HasUpperNoiseFullOracle macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R μ L ρg B a P := by
  intro instM instB instS σf σg
  exact sourceUpperNoise_full_oracles macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R
    μ L ρg B a P hO σf σg

end Bilevel.ChiHierarchyHaar
