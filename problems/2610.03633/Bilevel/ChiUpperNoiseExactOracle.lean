import Bilevel.ChiUpperNoiseOracleProperty
import Bilevel.BernoulliNoiseless

/-! The zero-variance specialization uses the very same original response
and stream as the expected-query theorem. Its replies are exact on one common
probability-one seed event, simultaneously for every query. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry ChiUpperNoise
variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ)

def NoiselessUpperNoiseOriginal (μ L ρg B : ℝ) (hB : 0<B)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim)
    (P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (Y:=Blocks 1 (EuclideanGaussian.Space dim)) μ L L L ρg) : Prop :=
  ∀ᵐ coin ∂BernoulliOracle.law (BernoulliOracle.probability B 0) (BernoulliOracle.probability_le_one hB),
    ∀ q,sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
      (sc.curvature/24) rad R (publicLower μ L) (BernoulliOracle.probability B 0) a q coin=
      (pack (P.fx q.fst q.snd) (P.fy q.fst q.snd),pack (P.gx q.fst q.snd) (P.gy q.fst q.snd))

theorem HasUpperNoiseFullOracle.noiseless (μ L ρg B : ℝ) (hB : 0<B)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim)
    (P : Model.Primitive (X:=Joint (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))
      (Y:=Blocks 1 (EuclideanGaussian.Space dim)) μ L L L ρg)
    (hO : HasUpperNoiseFullOracle macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R μ L ρg B a P) :
    NoiselessUpperNoiseOriginal macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R μ L ρg B hB a P := by
  letI : MeasurableSpace (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim))) := borel _
  letI : BorelSpace (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim))) := ⟨rfl⟩
  obtain ⟨hB',Of,Og,hf,hg,he⟩ := hO 0 0
  have hOf := BernoulliOracle.oracle_uniform_exact hB' Of
  have hOg := BernoulliOracle.oracle_uniform_exact hB' Og
  filter_upwards [hOf,hOg] with coin hcF hcG
  intro q
  rw [←he,hcF,hcG,hf,hg]

end Bilevel.ChiHierarchyHaar
