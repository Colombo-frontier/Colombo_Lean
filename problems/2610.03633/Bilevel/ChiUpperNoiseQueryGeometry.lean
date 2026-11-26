import Bilevel.PrimitiveQueryGeometry
import Bilevel.ChiUpperNoiseOracleProperty
import Bilevel.ChiUpperNoiseExpectedQueries

/-! Public finite geometry and actual globally conservative sample scalars
for the direct upper-noise family. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry ChiCarrier ChiUpperNoise ChiHierarchyHaar
set_option autoImplicit false

def upperNoiseGeometry (dim : ℕ) (hD : 0<dim) : Geometry := by
  letI : NeZero dim := ⟨hD.ne'⟩
  letI : MeasurableSpace (UpperNoiseOutput dim) := borel _
  letI : BorelSpace (UpperNoiseOutput dim) := ⟨rfl⟩
  letI : MeasurableSpace (Blocks 1 (EuclideanGaussian.Space dim)) := borel _
  letI : BorelSpace (Blocks 1 (EuclideanGaussian.Space dim)) := ⟨rfl⟩
  letI : MeasurableSpace (UpperNoiseQuery dim) := borel _
  letI : BorelSpace (UpperNoiseQuery dim) := ⟨rfl⟩
  exact Geometry.of (UpperNoiseOutput dim) (Blocks 1 (EuclideanGaussian.Space dim))

end Bilevel.PrimitiveQuery

namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiUpperNoise
set_option autoImplicit false
variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ)

theorem sourceUpperNoiseJoint_conservative (μ L π : ℝ)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim) (coin : Bool) :
    ∃ f g : UpperNoiseQuery dim → ℝ,
      (∀ q,HasGradientAt f
        (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
          (sc.curvature/24) rad R (publicLower μ L) π a q coin).1 q) ∧
      (∀ q,HasGradientAt g
        (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
          (sc.curvature/24) rad R (publicLower μ L) π a q coin).2 q) := by
  let M := sourceCanonicalMacro macroN 0 dim cn ratios resolutions hAll a sc Km
  let D := sourceCanonicalGeometry macroN 0 dim cn ratios resolutions hdim a sc weight 3 1 ζ CR
  let f := fullCore 1 M (sc.curvature/24) D rad R
  let f₀ := fullInactiveCore 1 M (sc.curvature/24) D rad R
  have hf : Differentiable ℝ f := (fullCore_contDiff _ _ _ _ _ _).differentiable (by norm_num)
  have hf₀ : Differentiable ℝ f₀ := (fullInactiveCore_contDiff _ _ _ _ _ _).differentiable (by norm_num)
  have hg : Differentiable ℝ (publicLower μ L : UpperNoiseQuery dim → ℝ) :=
    (ChiQuadratic.lower_contDiff _ _ 3).differentiable (by norm_num)
  refine ⟨ChiConservative.samplePotential f f₀ π coin,publicLower μ L,?_,?_⟩
  · exact fun q => ChiConservative.sample_hasGradientAt f f₀ hf hf₀ π coin q
  · exact fun q => (hg q).hasGradientAt

end Bilevel.ChiHierarchyHaar
