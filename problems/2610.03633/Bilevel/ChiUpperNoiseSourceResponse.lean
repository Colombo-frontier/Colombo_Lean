import Bilevel.ChiUpperNoiseOriginalBorel
import Bilevel.ChiOriginalSourceDefinitions

/-! Literal original canonical upper-noise response. The upper sample is
the fixed conservative scalar pair; the public lower gradient is exact. -/
noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiUpperNoise

variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

def sourceUpperNoiseJoint (ν : ℝ) (ρ R : ℕ → ℝ)
    (g : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)) → ℝ) (π : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim)
    (q : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim))) (coin : Bool) :
    Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)) ×
      Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)) :=
  (ChiConservative.sampleGradient
    (fullCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν
      (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R)
    (fullInactiveCore 1 (sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km) ν
      (sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight A Kminus ζ CR) ρ R) π coin q,
    gradient g q)

theorem sourceUpperNoiseJoint_measurable
    [MeasurableSpace (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))]
    [BorelSpace (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)))]
    (ν : ℝ) (ρ R : ℕ → ℝ)
    (g : Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)) → ℝ)
    (hg : Continuous g) (π : ℝ) :
    Measurable (fun p : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim ×
        (Queries (EuclideanGaussian.Space dim) (Blocks 1 (EuclideanGaussian.Space dim)) × Bool) =>
      sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
        ν ρ R g π p.1 p.2.1 p.2.2) := by
  exact originalPair_measurable 1
    (sourceTemplateMacro macroN 0 dim cn ratios resolutions hAll sc Km) ν
    (sourceTemplateGeometry macroN 0 dim cn ratios resolutions hdim sc weight A Kminus ζ CR) ρ R
    (fun a => frame hAll a (Sum.inl ())) (canonicalFamily hdim)
    (sourceCompleteData_measurable macroN 0 dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km) g hg π

end Bilevel.ChiHierarchyHaar
