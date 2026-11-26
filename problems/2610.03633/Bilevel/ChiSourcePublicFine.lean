import Bilevel.ChiSourcePublicCap
import Bilevel.ChiSourceHorizonDimension

/-! The finest normal width and hence the observer cap are literal public
scalars. In particular, selecting the ambient dimension does not require
first constructing a frame in that dimension. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive

def sourcePublicEll (initial : Scale) (ratios resolutions : ℕ → ℝ) (J : ℕ) : ℝ :=
  ratios J*(parentScale initial ratios resolutions J).curvature

def sourcePublicWidth (initial : Scale) (ratios resolutions : ℕ → ℝ) (J : ℕ) : ℝ :=
  resolutions J*(parentScale initial ratios resolutions J).width/ratios J

def sourcePublicFineParameter (initial : Scale) (ratios resolutions : ℕ → ℝ)
    (J : ℕ) (ρ μ L Cf : ℝ) : ℝ :=
  fineParameter ρ (3*μ/2) (sourcePublicEll initial ratios resolutions J) (normalCoefficient L J) Cf J

def sourcePublicFinestWidth (initial : Scale) (ratios resolutions : ℕ → ℝ)
    (J : ℕ) (c v : ℝ) : ℝ :=
  ZeroChainSchedule.width c (sourcePublicWidth initial ratios resolutions J) v (ZeroChainSchedule.levels v)

theorem sourcePublicFinestWidth_pos (initial : Scale) (ratios resolutions : ℕ → ℝ)
    (J : ℕ) (c v : ℝ) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hc : 0<c) (hv : 1≤v) :
    0<sourcePublicFinestWidth initial ratios resolutions J c v := by
  have hp := parentScale_positive initial ratios resolutions hl hw hr hη J
  have hwidth : 0<sourcePublicWidth initial ratios resolutions J :=
    div_pos (mul_pos (hη J) hp.2) ((by norm_num : (0:ℝ)<1).trans_le (hr J))
  exact ZeroChainSchedule.width_pos c _ v hc hwidth hv _

end Bilevel.ChiExtensionCalibration

namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)

theorem sourceCanonical_ell_public (j : ℕ) (I : List ℕ) :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).ell=
      sourcePublicEll initial ratios resolutions j := rfl

theorem sourceCanonical_fineParameter_public (ρ μ L Cf : ℝ) :
    fineParameter ρ (3*μ/2)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR J []).ell
      (normalCoefficient L J) Cf J=sourcePublicFineParameter initial ratios resolutions J ρ μ L Cf := rfl

theorem sourceCanonical_finestWidth_public (c v : ℝ) :
    ZeroChainSchedule.width c
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR J []).width
      v (ZeroChainSchedule.levels v)=sourcePublicFinestWidth initial ratios resolutions J c v := rfl

end Bilevel.ChiHierarchyHaar
