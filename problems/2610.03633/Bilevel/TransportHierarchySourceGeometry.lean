import Bilevel.TransportHierarchyFamily
import Bilevel.ChiSourcePublicCap

/-! Literal source nodes under the physical network/auxiliary prior.
The numerical widths, radii and frame sizes remain public and unchanged;
only the deepest frames use disjoint blocks of the one network frame. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyHaar ChiOuter
set_option maxHeartbeats 700000

variable (macroN J n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (s : PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)

def sourcePhysicalMacro (initial : Scale) (Km : ℝ) : Node (EuclideanGaussian.Space D) :=
  sourceMacroNode macroN initial Km (physicalMacroFrame hAll s)

def sourcePhysicalGeometry (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ) :
    Geometry (EuclideanGaussian.Space D) :=
  sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR (physicalFamily hdim hT s)

theorem sourcePhysicalMacro_frame (initial : Scale) (Km : ℝ) :
    (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km).frame=
      physicalMacroFrame hAll s := rfl

theorem sourcePhysicalGeometry_frame (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR : ℝ) (j : ℕ) (I : List ℕ) :
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).frame=
      physicalFamily hdim hT s j I := rfl

theorem sourcePhysicalGeometry_width (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR : ℝ) (j : ℕ) (I : List ℕ) :
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).width=
      resolutions j*(parentScale initial ratios resolutions j).width/ratios j := rfl

theorem sourcePhysicalGeometry_radius (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR : ℝ) (j : ℕ) (I : List ℕ) :
    (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR j I).radius=
      sourceLocalRadius CR (parentScale initial ratios resolutions j).curvature
        (parentScale initial ratios resolutions j).width (ratios j) (weight j) ζ := rfl

theorem sourcePhysical_geometry (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR Km : ℝ) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km) :
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km
    let G := sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR
    0<M.width ∧ 0<M.radius ∧
    (∀ j I,0<(G j I).width ∧ 0<(G j I).radius ∧ 0<(G j I).ell ∧
      0<(G j I).parentWidth ∧ (G j I).width≤(G j I).parentWidth) ∧
    (∀ j I,(G j I).width=(G j []).width) :=
  source_inverse_geometry initial ratios resolutions weight A Kminus ζ cn CR Km macroN
    (physicalMacroFrame hAll s) (physicalFamily hdim hT s) hl hw hr hη hη1 hweight hζ hCR hKm

theorem sourcePhysical_cap_eq_public (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR Km τ : ℝ) :
    sourceProjectionCap (sourcePhysicalMacro macroN J n D cn ratios resolutions hAll s initial Km)
      (sourcePhysicalGeometry macroN J n D cn ratios resolutions hdim hT s initial weight A Kminus ζ CR) J τ=
      sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ := by
  apply congrArg₂ finiteProjectionCap
  · funext i
    rcases i with _|(_|_) <;> rfl
  · funext i
    rcases i with _|(_|_) <;> rfl

end Bilevel.TransportHierarchy
