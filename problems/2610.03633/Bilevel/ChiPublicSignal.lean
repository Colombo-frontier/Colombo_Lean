import Bilevel.ChiCanonicalPublicData
import Bilevel.ChiHierarchySignal

/-! The actual conservative signal amplitude is a positive public scalar,
so its Bernoulli law can be chosen before the observer dimension. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive

def sourcePublicAmplitude (sc : Scale) (ratios resolutions : ℕ → ℝ)
    (J : ℕ) (cms v μ L Bs : ℝ) : ℝ :=
  4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*sourcePublicEll sc ratios resolutions J*
    sourcePublicWidth sc ratios resolutions J*
    sourcePublicFinestWidth sc ratios resolutions J cms v/normalCoefficient L J)

theorem sourcePublicAmplitude_pos (sc : Scale) (ratios resolutions : ℕ → ℝ)
    (J : ℕ) (cms v μ L Bs : ℝ)
    (hl : 0<sc.curvature) (hw : 0<sc.width) (hr : ∀ j,1≤ratios j)
    (hres : ∀ j,0<resolutions j) (hJ : 1≤J) (hcms : 0<cms) (hv : 1≤v)
    (hμ : 0<μ) (hL : 0<L) (hBs : 0<Bs) :
    0<sourcePublicAmplitude sc ratios resolutions J cms v μ L Bs := by
  have hp := parentScale_positive sc ratios resolutions hl hw hr hres J
  have hrp : 0<ratios J := zero_lt_one.trans_le (hr J)
  have hell : 0<sourcePublicEll sc ratios resolutions J := mul_pos hrp hp.1
  have hwidth : 0<sourcePublicWidth sc ratios resolutions J := div_pos (mul_pos (hres J) hp.2) hrp
  have hW := sourcePublicFinestWidth_pos sc ratios resolutions J cms v hl hw hr hres hcms hv
  have hd := normalCoefficient_pos hL hJ
  have hC := SmallGapLiftSupport.C_pos
  unfold sourcePublicAmplitude
  positivity

end Bilevel.ChiExtensionCalibration
