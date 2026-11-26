import Bilevel.ChiFullDisclosureState

/-! Complete Haar-column representation of the original source objective.
Only the instance representation here has all columns; the algorithm still
uses the separate success-driven finite disclosed store. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  ChiPrefixEvaluation PrimitiveGeometry

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

def sourceTemplateMacro : ChiRecursive.Node (EuclideanGaussian.Space dim) :=
  sourceCanonicalMacro macroN J dim cn ratios resolutions hAll (fun _ => 1) initial Km

def sourceTemplateGeometry : Geometry (EuclideanGaussian.Space dim) :=
  sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim (fun _ => 1) initial weight A Kminus ζ CR

def sourceCompleteData : Orientations (sourceCounts macroN cn ratios resolutions) J dim →
    HierarchyData (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km)
      (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR) :=
  frameData _ _ (fun a => frame hAll a (Sum.inl ())) (canonicalFamily hdim)

theorem sourceCompleteData_measurable :
    Measurable (sourceCompleteData macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km) := by
  unfold sourceCompleteData frameData
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro k
    change Measurable (fun a : Orientations (sourceCounts macroN cn ratios resolutions) J dim =>
      frame hAll a (Sum.inl ()) (basis k))
    simp only [frame_basis]
    exact (measurable_pi_apply k).comp ((measurable_pi_apply (Sum.inl ())).comp (columns_measurable hAll))
  · apply measurable_pi_lambda
    intro j
    apply measurable_pi_lambda
    intro I
    apply measurable_pi_lambda
    intro k
    exact canonicalFamily_column_measurable (counts:=sourceCounts macroN cn ratios resolutions)
      (J:=J) (D:=dim) hdim j I k

theorem source_original_mean_loss_measurable (m : ℕ) (ν : ℝ) (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ)
    [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))]
    [BorelSpace (Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)))] :
    Measurable (fun p : Orientations (sourceCounts macroN cn ratios resolutions) J dim ×
        Joint (EuclideanGaussian.Space dim) (Blocks m (EuclideanGaussian.Space dim)) =>
      ‖gradient (jointOuter m
        (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll p.1 initial Km) ν
        (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim p.1 initial weight A Kminus ζ CR)
        ρ R d K) p.2‖) := by
  exact original_mean_loss_measurable m
    (sourceTemplateMacro macroN J dim cn ratios resolutions hAll initial Km) ν
    (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR)
    ρ R d K (fun a => frame hAll a (Sum.inl ())) (canonicalFamily hdim)
    (sourceCompleteData_measurable macroN J dim cn ratios resolutions hdim hAll initial weight A Kminus ζ CR Km)

end Bilevel.ChiHierarchyHaar
