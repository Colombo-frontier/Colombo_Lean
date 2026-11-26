import Bilevel.ChiOriginalSourceDefinitions

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


variable (m : ℕ) (c v : ℝ) (hc : 0<c) (hβ : 0<((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) J []).width)
  (hv : 1≤v) (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (rad R : ℕ → ℝ) (dn : ℝ)
  (δ : Bool → NNReal) (hδ : ∀ active,δ active<1)
  (hOriginal : ∀ (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)),ContDiff ℝ 3 (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn))
  (hOriginal2 : ∀ (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) z,‖iteratedFDeriv ℝ 2 (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn) z‖≤(δ active:ℝ))

variable (hR : ∀ i : Fin J,0<R (i.val+1)) (hw : ∀ i : Fin J,0<((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) (i.val+1) []).width)
  (h2 : ∀ active : Bool,∀ p : {p : VirtualState (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) | ValidState (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) (fun _ => ((sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km)).n+1) (fun _ => fullCounts (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR)) p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) J (fun _ => ((sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km)).n+1) (fun _ => fullCounts (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR))
      c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)

include hR hw h2 in
theorem sourceOriginalJoint_measurable
    [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))] [BorelSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))]
    [MeasurableSpace (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s))] [BorelSpace (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s))]
    [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s)))]
    [BorelSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s)))]
    [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s))]
    [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s))]
    (ν ρ Rbase : ℝ) (b : Normals s) (μ L π : ℝ) :
    Measurable (fun p : ((Orientations (sourceCounts macroN cn ratios resolutions) J dim) × FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s)) × Bool =>
      sourceOriginalJoint macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km
        m c v hc hβ hv s index radialIndex fineIndex rad R dn δ hδ hOriginal hOriginal2
        ν ρ Rbase b μ L π p.1.1 p.1.2 p.2) := by
  let Q := FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s)
  letI : SecondCountableTopology (Blocks m (EuclideanGaussian.Space dim)) := inferInstance
  letI : SecondCountableTopology (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim))) := inferInstance
  letI : SecondCountableTopology (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s)) := inferInstance
  letI : SecondCountableTopology Q :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim))) (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s))).toHomeomorph.secondCountableTopology
  have hupper := source_original_upper_reply_measurable macroN J dim cn ratios resolutions hdim hAll
    initial weight A Kminus ζ CR Km m s ν ρ Rbase J b
  have hlower (active : Bool) := source_original_lower_reply_measurable macroN J dim cn ratios resolutions hdim hAll
    initial weight A Kminus ζ CR Km active m c v hc hβ hv s index radialIndex fineIndex rad R dn
    hR hw (h2 active) (δ active) (hδ active) (hOriginal active) (hOriginal2 active) μ L
  let f : Orientations (sourceCounts macroN cn ratios resolutions) J dim → Q → ℝ := fun a =>
    fullUpper (upperBase m (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km) ν
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR) J ρ Rbase) b
  let g : Bool → Orientations (sourceCounts macroN cn ratios resolutions) J dim → Q → ℝ :=
    sourceOriginalLower macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km
      m c v hc hβ hv s index radialIndex fineIndex rad R dn δ hδ hOriginal hOriginal2 μ L
  have hf : Measurable (fun p : Orientations (sourceCounts macroN cn ratios resolutions) J dim × Q =>
      gradient (f p.1) p.2) := hupper
  have hg (active : Bool) : Measurable (fun p : Orientations (sourceCounts macroN cn ratios resolutions) J dim × Q =>
      gradient (g active p.1) p.2) := hlower active
  exact ChiConservative.parametric_fullPair_measurable f (g true) (g false) hf (hg true) (hg false) π

end Bilevel.ChiHierarchyHaar

namespace Bilevel.ChiPrefixEvaluation
open ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ) (c v : ℝ)
  (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v) (s : ℕ)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)

@[simp] theorem originalPotential_true :
    originalPotential true m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn=
      hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn := rfl

@[simp] theorem originalPotential_false :
    originalPotential false m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn=
      hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn := rfl

end Bilevel.ChiPrefixEvaluation


