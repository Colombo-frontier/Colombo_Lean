import Bilevel.PolishedLiteralInactivePieces
import Bilevel.ZeroChainSchedule

/-! The original final blind resolution fits inside every inactive
multiscale flattening core, for the actual displayed schedule. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open ZeroChainSchedule

theorem aExponent_le_final_b (J j : ℕ) (hj : j<J) : aExponent j≤bExponent J := by
  have hp : (4:ℝ)^(j+1)≤4^J := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : 0<(4:ℝ)^(j+1) := by positivity
  have hJpos : 0<(4:ℝ)^J := by positivity
  have hden : (4:ℝ)^(j+1)≤2*4^J := by linarith
  have hh : 1/(2*(4:ℝ)^J)≤1/(4:ℝ)^(j+1) := one_div_le_one_div_of_le hpos hden
  unfold aExponent bExponent
  linarith

theorem final_width_le_resolution (c β θ : ℝ) (hc : 0≤c) (hβ : 0≤β) (hθ : 1≤θ)
    (j : ℕ) (hj : j<levels θ) : width c β θ (levels θ)≤resolution c β θ j := by
  unfold width resolution
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hθ (neg_le_neg (aExponent_le_final_b _ _ hj)))
    (mul_nonneg hc hβ)

theorem source_blind_resolution_fits (c β θ : ℝ) (hc : 0<c) (hβ : 0<β) (hθ : 1≤θ)
    (j : ℕ) (hj : j<levels θ) :
    width c β θ (levels θ)/8≤resolution c β θ j := by
  have hw := width_pos c β θ hc hβ hθ (levels θ)
  exact (by linarith : width c β θ (levels θ)/8≤width c β θ (levels θ)).trans
    (final_width_le_resolution c β θ hc.le hβ.le hθ j hj)

end Bilevel.PolishedLiteral
