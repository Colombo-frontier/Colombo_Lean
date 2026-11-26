import Bilevel.ChiOriginalHaarReply

/-! Named original source loss and literal joint SFO response, jointly Borel
in the finite Haar orientation, arbitrary query, and independent coin. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension PartialLegendre ChiUpper

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)


def sourceOriginalLoss (m : ℕ) (ν : ℝ) (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ)
    (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) (x : Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim))) : ℝ :=
  ‖gradient (jointOuter m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km) ν ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) ρ R d K) x‖

theorem sourceOriginalLoss_measurable (m : ℕ) (ν : ℝ) (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ)
    [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))] [BorelSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))] :
    Measurable (Function.uncurry (sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll
      initial weight A Kminus ζ CR Km m ν ρ R d K)) :=
  source_original_mean_loss_measurable macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km
    m ν ρ R d K

theorem sourceOriginal_width_pos
    (hβ : 0<(sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR J []).width)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) :
    0<(sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR J []).width := hβ
variable (m : ℕ) (c v : ℝ) (hc : 0<c) (hβ : 0<((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) J []).width)
  (hv : 1≤v) (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (rad R : ℕ → ℝ) (dn : ℝ)
  (δ : Bool → NNReal) (hδ : ∀ active,δ active<1)
  (hOriginal : ∀ (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)),ContDiff ℝ 3 (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn))
  (hOriginal2 : ∀ (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) z,‖iteratedFDeriv ℝ 2 (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn) z‖≤(δ active:ℝ))

def sourceOriginalLower (μ L : ℝ) (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) : FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s) → ℝ :=
  fullExtensionLower (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km) ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR)
    J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn)
    (hOriginal active a) (δ active) (hOriginal2 active a) (hδ active) μ L

def sourceOriginalJoint (ν ρ Rbase : ℝ) (b : Normals s) (μ L π : ℝ)
    (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) (q : FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s)) (coin : Bool) :
    FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s) × FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s) :=
  let g := sourceOriginalLower macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km
    m c v hc hβ hv s index radialIndex fineIndex rad R dn δ hδ hOriginal hOriginal2 μ L
  (gradient (fullUpper (upperBase m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km) ν ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) J ρ Rbase) b) q,
    ChiConservative.sampleGradient (g true a) (g false a) π coin q)

end Bilevel.ChiHierarchyHaar


