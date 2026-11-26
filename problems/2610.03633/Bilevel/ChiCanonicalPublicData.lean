import Bilevel.ChiCanonicalSourceNumeric
import Bilevel.ChiSourcePublicFine

/-! Literal public radial and fine parameters, independent of ambient
dimension and orientation, for the canonical source family. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive ChiBoundedChain

def sourcePublicRadialWeight (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (ζ : ℝ) (j : ℕ) : ℝ := weight j*(ζ*(parentScale initial ratios resolutions j).curvature)

def sourcePublicNodeRadius (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (CR ζ : ℝ) (j : ℕ) : ℝ := sourceLocalRadius CR
  (parentScale initial ratios resolutions j).curvature (parentScale initial ratios resolutions j).width
  (ratios j) (weight j) ζ

theorem sourcePublicNodeRadius_pos (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (CR ζ : ℝ) (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1≤ratios j) (hres : ∀ j,0<resolutions j) (hweight : ∀ j,0<weight j)
    (hCR : 0<CR) (hζ : 0<ζ) (j : ℕ) : 0<sourcePublicNodeRadius initial ratios resolutions weight CR ζ j := by
  have hp := parentScale_positive initial ratios resolutions hl hw hr hres j
  exact source_radial_radius_pos hCR hp.1 hp.2 (lt_of_lt_of_le zero_lt_one (hr j)) (hweight j) hζ

end Bilevel.ChiExtensionCalibration

namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)

theorem sourceCanonical_width_public (j : ℕ) (I : List ℕ) :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).width=
      sourcePublicWidth initial ratios resolutions j := rfl

theorem sourceCanonical_radial_function_public :
    (fun j => weight j*(sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j []).nu)=
      sourcePublicRadialWeight initial ratios resolutions weight ζ := rfl

theorem sourceCanonical_radius_function_public :
    (fun j => (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j []).radius)=
      sourcePublicNodeRadius initial ratios resolutions weight CR ζ := rfl

theorem sourceCanonical_fine_budget_public (ρ μ L Cf Bs cms : ℝ) :
    let D := sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR
    let v := fineParameter ρ (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J
    4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*(D J []).ell*(D J []).width*
      ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v)/normalCoefficient L J)=
    4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*sourcePublicEll initial ratios resolutions J*
      sourcePublicWidth initial ratios resolutions J*
      sourcePublicFinestWidth initial ratios resolutions J cms
        (sourcePublicFineParameter initial ratios resolutions J ρ μ L Cf)/normalCoefficient L J) := rfl

end Bilevel.ChiHierarchyHaar
