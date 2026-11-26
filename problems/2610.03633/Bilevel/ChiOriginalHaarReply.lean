import Bilevel.ChiOriginalBorelHaar
import Bilevel.ChiOriginalBorelSample

/-! Joint Borel replies for the actual canonical finite Haar source family. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option autoImplicit false
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry ChiExtension PartialLegendre ChiUpper

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)


variable (active : Bool) (m : ℕ) (c v : ℝ) (hc : 0<c) (hβ : 0<((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) J []).width)
  (hv : 1≤v) (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (rad R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
  (hw : ∀ i : Fin J,0<((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) (i.val+1) []).width)
  (h2 : ∀ p : {p : VirtualState (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) | ValidState (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) (fun _ => ((sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km)).n+1) (fun _ => fullCounts (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR)) p},∀ z,
    ‖iteratedFDeriv ℝ 2 (statePotential active m (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) J (fun _ => ((sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km)).n+1) (fun _ => fullCounts (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR))
      c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
  (δ : NNReal) (hδ : δ<1)
  (hOriginal : ∀ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),ContDiff ℝ 3 (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) J c v hc hβ hv s index radialIndex fineIndex rad R dn))
  (hOriginal2 : ∀ (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) z,‖iteratedFDeriv ℝ 2 (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a initial Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a initial weight A Kminus ζ CR) J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤(δ:ℝ))

include hR hw h2 hβ hOriginal hOriginal2 in
theorem source_original_lower_reply_measurable
    [MeasurableSpace (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s))] [BorelSpace (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s))]
    [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s)))]
    [BorelSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks m (EuclideanGaussian.Space dim)) (Normals s)))]
    [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s))]
    [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s))] (μ L : ℝ) :
    Measurable (fun p : (Orientations (sourceCounts macroN cn ratios resolutions) J dim) × FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s) =>
      gradient (fullExtensionLower (originalPotential active m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) p.1 initial Km)
        ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) p.1 initial weight A Kminus ζ CR) J c v hc hβ hv s index radialIndex fineIndex rad R dn)
        (hOriginal p.1) δ (hOriginal2 p.1) hδ μ L) p.2) := by
  exact original_lower_reply_measurable active m (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) J c v hc hβ hv s index radialIndex fineIndex rad R dn
    hR hw h2 (fun a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim) => frame hAll a (Sum.inl ()))
    (canonicalFamily (counts:=sourceCounts macroN cn ratios resolutions) (J:=J) (D:=dim) hdim)
    δ hδ hOriginal hOriginal2
    (sourceCompleteData_measurable macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km) μ L

omit active c v hc hβ hv index radialIndex fineIndex rad R dn hR hw h2 δ hδ hOriginal hOriginal2 in
theorem source_original_upper_reply_measurable (ν ρ Rbase : ℝ) (d : ℕ)
    [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))] [BorelSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))]
    [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s))]
    [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s))] (b : Normals s) :
    Measurable (fun p : (Orientations (sourceCounts macroN cn ratios resolutions) J dim) × FullNormalVariables (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) (Normals s) =>
      gradient (fullUpper (upperBase m ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) p.1 initial Km) ν
        ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) p.1 initial weight A Kminus ζ CR) d ρ Rbase) b) p.2) := by
  exact original_upper_reply_measurable m (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) ν (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) d ρ Rbase s b
    (fun a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim) => frame hAll a (Sum.inl ()))
    (canonicalFamily (counts:=sourceCounts macroN cn ratios resolutions) (J:=J) (D:=dim) hdim)
    (sourceCompleteData_measurable macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km)

end Bilevel.ChiHierarchyHaar
