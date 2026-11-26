import Bilevel.ChiCanonicalSourceFields
import Bilevel.ChiSourceProjectionCap

/-! A public positive energy cap for the actual sampled source. It is
definitionally independent of every Haar orientation, and simultaneously
pays all macro/inner blind widths and the finest normal width. -/
noncomputable section
set_option maxHeartbeats 200000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiOuter ChiExtensionCalibration

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "M" => sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km
local notation "G" => sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR


theorem sourceCanonical_cap_independent (τ : ℝ)
    (a' : Orientations (sourceCounts macroN cn ratios resolutions) J dim) :
    sourceProjectionCap M G J τ=
      sourceProjectionCap (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a' initial Km)
        (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a' initial weight A Kminus ζ CR) J τ := by
  let M' := sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a' initial Km
  let G' := sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a' initial weight A Kminus ζ CR
  have hR : sourceProjectionRadius M G J=sourceProjectionRadius M' G' J := by
    funext i
    rcases i with _|(_|_) <;> simp only [sourceProjectionRadius,sourceProjectionThreshold,
      M',G',sourceCanonicalMacro_radius,sourceCanonicalMacro_width,sourceCanonicalGeometry_radius,sourceCanonicalGeometry_width]
  have hT : sourceProjectionThreshold M G J τ=sourceProjectionThreshold M' G' J τ := by
    funext i
    rcases i with _|(_|_) <;> simp only [sourceProjectionRadius,sourceProjectionThreshold,
      M',G',sourceCanonicalMacro_radius,sourceCanonicalMacro_width,sourceCanonicalGeometry_radius,sourceCanonicalGeometry_width]
  change finiteProjectionCap (sourceProjectionRadius M G J) (sourceProjectionThreshold M G J τ)=
    finiteProjectionCap (sourceProjectionRadius M' G' J) (sourceProjectionThreshold M' G' J τ)
  rw [hR,hT]


theorem sourceCanonical_cap_certificate
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (τ : ℝ) (hτ : 0<τ) :
    0<sourceProjectionCap M G J τ ∧ sourceProjectionCap M G J τ≤1 ∧
    (M).radius*Real.sqrt (sourceProjectionCap M G J τ)≤(M).width/8 ∧
    (∀ j,j≤J → (G j []).radius*Real.sqrt (sourceProjectionCap M G J τ)≤(G j []).width/8) ∧
    (G J []).radius*Real.sqrt (sourceProjectionCap M G J τ)≤τ/16 := by
  have hg := source_inverse_geometry initial ratios resolutions weight A Kminus ζ cn CR Km macroN
    (frame hAll a (Sum.inl ())) (canonicalFamily hdim a) hl hw hr hη hη1 hweight hζ hCR hKm
  exact sourceProjectionCap_certificate M G J τ hg.2.1.le hg.1
    (fun j _ => (hg.2.2.1 j []).2.1.le) (fun j _ => (hg.2.2.1 j []).1) hτ

end Bilevel.ChiHierarchyHaar
