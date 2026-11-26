import Bilevel.ChiSourcePublicCap

/-! All radius budgets of the public source cap, stated entirely in
public scalars before any ambient dimension or frame is introduced. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem sourcePublicCap_budgets (macroN J : ℕ) (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (CR ζ Km τ : ℝ) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hweight : ∀ j,0<weight j)
    (hCR : 0<CR) (hζ : 0<ζ) (hKm : 0<Km) (hτ : 0<τ) :
    0<sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ ∧
    sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ≤1 ∧
    ∀ i,sourcePublicRadius macroN J initial ratios resolutions weight CR ζ Km i*
      Real.sqrt (sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ)≤
        sourcePublicThreshold J initial ratios resolutions τ i := by
  have hp := parentScale_positive initial ratios resolutions hl hw hr hη
  have hrp (j : ℕ) : 0<ratios j := lt_of_lt_of_le zero_lt_one (hr j)
  have hR (j : ℕ) : 0<sourceLocalRadius CR (parentScale initial ratios resolutions j).curvature
      (parentScale initial ratios resolutions j).width (ratios j) (weight j) ζ :=
    source_radial_radius_pos hCR (hp j).1 (hp j).2 (hrp j) (hweight j) hζ
  exact finiteProjectionCap_bounds
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

end Bilevel.ChiExtensionCalibration
