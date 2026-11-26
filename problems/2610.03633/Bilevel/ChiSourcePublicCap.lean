import Bilevel.ChiCanonicalSourceFields
import Bilevel.ChiSourceProjectionCap

/-! Dimension-independent public energy cap. Its definition contains no
Haar sample, frame, ambient space, or dimension, so the observer dimension
can be selected afterward without a circular parameter choice. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive

def sourcePublicRadius (macroN J : ℕ) (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (CR ζ Km : ℝ) : Unit ⊕ (Fin (J+1) ⊕ Unit) → ℝ
  | Sum.inl _ => Km*initial.width*Real.sqrt ((macroN:ℝ)+1)
  | Sum.inr (Sum.inl j) => sourceLocalRadius CR (parentScale initial ratios resolutions j.val).curvature
      (parentScale initial ratios resolutions j.val).width (ratios j.val) (weight j.val) ζ
  | Sum.inr (Sum.inr _) => sourceLocalRadius CR (parentScale initial ratios resolutions J).curvature
      (parentScale initial ratios resolutions J).width (ratios J) (weight J) ζ

def sourcePublicThreshold (J : ℕ) (initial : Scale) (ratios resolutions : ℕ → ℝ)
    (τ : ℝ) : Unit ⊕ (Fin (J+1) ⊕ Unit) → ℝ
  | Sum.inl _ => initial.width/8
  | Sum.inr (Sum.inl j) => (resolutions j.val*(parentScale initial ratios resolutions j.val).width/ratios j.val)/8
  | Sum.inr (Sum.inr _) => τ/16

def sourcePublicCap (macroN J : ℕ) (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (CR ζ Km τ : ℝ) : ℝ :=
  finiteProjectionCap (sourcePublicRadius macroN J initial ratios resolutions weight CR ζ Km)
    (sourcePublicThreshold J initial ratios resolutions τ)

theorem sourcePublicCap_positive (macroN J : ℕ) (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (CR ζ Km τ : ℝ) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hweight : ∀ j,0<weight j)
    (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) (hτ : 0<τ) :
    0<sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ ∧
      sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ≤1 := by
  have hp := parentScale_positive initial ratios resolutions hl hw hr hη
  have hrp (j : ℕ) : 0<ratios j := lt_of_lt_of_le zero_lt_one (hr j)
  have hR (j : ℕ) : 0<sourceLocalRadius CR (parentScale initial ratios resolutions j).curvature
      (parentScale initial ratios resolutions j).width (ratios j) (weight j) ζ :=
    source_radial_radius_pos hCR (hp j).1 (hp j).2 (hrp j) (hweight j) hζ
  have h := finiteProjectionCap_bounds
    (sourcePublicRadius macroN J initial ratios resolutions weight CR ζ Km)
    (sourcePublicThreshold J initial ratios resolutions τ)
    (by rintro (_|(j|_))
        · change 0≤Km*initial.width*Real.sqrt ((macroN:ℝ)+1);positivity
        · exact (hR j.val).le
        · exact (hR J).le)
    (by rintro (_|(j|_))
        · exact div_pos hw (by norm_num)
        · exact div_pos (div_pos (mul_pos (hη j.val) (hp j.val).2) (hrp j.val)) (by norm_num)
        · exact div_pos hτ (by norm_num))
  exact ⟨h.1,h.2.1⟩

end Bilevel.ChiExtensionCalibration

namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration

theorem sourceCanonical_cap_eq_public (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
    (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km τ : ℝ) :
    sourceProjectionCap (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR) J τ=
      sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ := by
  apply congrArg₂ finiteProjectionCap
  · funext i
    rcases i with _|(_|_) <;>
      simp only [sourceProjectionRadius,sourcePublicRadius,sourceCanonicalMacro_radius,sourceCanonicalGeometry_radius]
  · funext i
    rcases i with _|(_|_) <;>
      simp only [sourceProjectionThreshold,sourcePublicThreshold,sourceCanonicalMacro_width,sourceCanonicalGeometry_width]

end Bilevel.ChiHierarchyHaar
