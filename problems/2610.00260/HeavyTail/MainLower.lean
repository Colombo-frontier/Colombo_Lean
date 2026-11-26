import HeavyTail.MaskedMinimax
import HeavyTail.ConfidenceKernelLower
import HeavyTail.AtMostModel

/-! The complete lower half of the manuscript's unified all-budget theorem,
for the actual public/private oracle model and arbitrary randomized adaptive
algorithms. The three proved oracle families share the public quadratic block. -/

open MeasureTheory
open scoped ENNReal
namespace HeavyTail
noncomputable section

def statisticalAmplitude (L s p δ : ℝ) (T : ℕ) : ℝ :=
  L / Real.sqrt T + s * (((L ^ 2 / s ^ 2) + Real.log (3 / δ)) / T) ^ (1 - 1 / p)

theorem statisticalAmplitude_le_components (θ : OracleParameters) :
    statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T ≤
      θ.L / Real.sqrt θ.T + MaskedLower.heavyCoefficient θ.L θ.s θ.p θ.T +
        θ.s * (confidenceLog θ.δ / θ.T) ^ (1 - 1 / θ.p) := by
  have hq := MaskedLower.heavyExponent_range θ.p_gt_one θ.p_le_two
  have hlog := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hpow := Real.rpow_add_le_add_rpow
    (by positivity : 0 ≤ (θ.L ^ 2 / θ.s ^ 2) / θ.T)
    (div_nonneg hlog.le (Nat.cast_nonneg θ.T)) hq.1 (by linarith : 1 - 1 / θ.p ≤ 1)
  have hm := mul_le_mul_of_nonneg_left hpow θ.s_pos.le
  unfold statisticalAmplitude MaskedLower.heavyCoefficient
  rw [add_div]
  dsimp [confidenceLog] at hm ⊢
  linarith

theorem envelope_lower_from_third {μ D G w x : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hw : 0 ≤ w) (hx : 0 ≤ x)
    (hbound : w ≤ 3 * x) :
    (1 / 147456 : ℝ) * envelope μ D (min G w) ≤
      (1 / 16384 : ℝ) * envelope μ D (min G x) := by
  have hcap : (1 / 3 : ℝ) * min G w ≤ min G x := by
    apply le_min
    · have h := min_le_left G w
      nlinarith
    · have h := min_le_right G w
      nlinarith
  have hscale := envelope_scale_lower hμ hD (le_min hG hw)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hm := envelope_mono hμ hD (by positivity) hcap
  nlinarith

theorem three_component_minimax_lower {μ D G w x y z : ℝ} {R : ℝ≥0∞}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hw : 0 ≤ w)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hwxyz : w ≤ x + y + z)
    (hX : ENNReal.ofReal ((1 / 16384 : ℝ) * envelope μ D (min G x)) ≤ R)
    (hY : ENNReal.ofReal ((1 / 16384 : ℝ) * envelope μ D (min G y)) ≤ R)
    (hZ : ENNReal.ofReal ((1 / 16384 : ℝ) * envelope μ D (min G z)) ≤ R) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope μ D (min G w)) ≤ R := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact (ENNReal.ofReal_le_ofReal (envelope_lower_from_third hμ hD hG hw hz
        (by linarith))).trans hZ
    · exact (ENNReal.ofReal_le_ofReal (envelope_lower_from_third hμ hD hG hw hy
        (by linarith))).trans hY
  · rcases le_total x z with hxz | hzx
    · exact (ENNReal.ofReal_le_ofReal (envelope_lower_from_third hμ hD hG hw hz
        (by linarith))).trans hZ
    · exact (ENNReal.ofReal_le_ofReal (envelope_lower_from_third hμ hD hG hw hx
        (by linarith))).trans hX

/-- The lower half of `thm:main`, with the explicit universal constant 1/147456. -/
theorem unified_fixedCallMinimax_lower {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope θ.μ θ.D
      (min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T))) ≤ fixedCallMinimax (HardSpace d) θ := by
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hlog := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hlog' : 0 < Real.log (3 / θ.δ) := hlog
  have hd : 0 < d := lt_of_lt_of_le (MaskedLower.activeDimension_bounds θ.s_pos θ.s_le_L).1 hdim
  let e : HardSpace d := EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hconfidence := confidence_fixedCallMinimax_lower θ e he hT
  have hc : ENNReal.ofReal ((1 / 16384 : ℝ) * envelope θ.μ θ.D
      (min θ.G (θ.s * (confidenceLog θ.δ / θ.T) ^ (1 - 1 / θ.p)))) ≤ fixedCallMinimax (HardSpace d) θ := by
    apply le_trans _ hconfidence
    apply ENNReal.ofReal_le_ofReal
    unfold confidenceRate
    have hn : 0 ≤ envelope θ.μ θ.D
        (min θ.G (θ.s * (confidenceLog θ.δ / θ.T) ^ (1 - 1 / θ.p))) :=
      envelope_nonneg θ.μ_nonneg θ.D_pos.le (by positivity)
    nlinarith
  apply three_component_minimax_lower θ.μ_nonneg θ.D_pos.le θ.G_pos.le
    (by unfold statisticalAmplitude; positivity) (by positivity)
    (by unfold MaskedLower.heavyCoefficient; positivity) (by positivity)
    (statisticalAmplitude_le_components θ)
  · exact GaussianLower.gaussian_fixedCallMinimax_lower_of_dimension θ hT hdim
  · exact MaskedLower.masked_fixedCallMinimax_lower θ hT hdim
  · exact hc

/-- The same lower bound covers actual algorithms stopping almost surely by T. -/
theorem unified_atMostCallMinimax_lower {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope θ.μ θ.D
      (min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T))) ≤ atMostCallMinimax (HardSpace d) θ := by
  rw [atMostCallMinimax_eq_fixedCallMinimax]
  exact unified_fixedCallMinimax_lower θ hT hdim

end
end HeavyTail
