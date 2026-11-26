import Bilevel.CachedParameterChoice

/-! Exact radius/noise identities and the anchor-only extra variance cost.
These statements include zero upper smoothness and zero noise. -/
noncomputable section
namespace Bilevel.CachedParameterChoice

theorem inverse_tilt_sq (E ε : ℝ) :
    1/(tilt E ε)^2 ≤ 1+(64*E/ε)^2 := by
  unfold tilt
  split_ifs with h
  · simp only [one_pow, div_one]
    nlinarith [sq_nonneg (64*E/ε)]
  · rw [min_def]
    split_ifs
    · simp only [one_pow, div_one]
      nlinarith [sq_nonneg (64*E/ε)]
    · have he : 1/(ε/(64*E))^2 = (64*E/ε)^2 := by
        rw [one_div, ← inv_pow, inv_div]
      rw [he]
      linarith

theorem inverse_anchor_sq (Lf Lg k E ε : ℝ) :
    1/(anchorRadius Lf Lg k E ε)^2 ≤
      1/(lowerRadius Lg E ε)^2 + (64*(1+k)*Lf/ε)^2 := by
  unfold anchorRadius
  split_ifs
  · nlinarith [sq_nonneg (64*(1+k)*Lf/ε)]
  · rw [min_def]
    split_ifs
    · nlinarith [sq_nonneg (64*(1+k)*Lf/ε)]
    · have he : 1/(ε/(64*(1+k)*Lf))^2 = (64*(1+k)*Lf/ε)^2 := by
        rw [one_div, ← inv_pow, inv_div]
      rw [he]
      have : 0 ≤ 1/(lowerRadius Lg E ε)^2 := by positivity
      linarith

theorem anchor_variance_split (Lf Lg k E ε μ σ : ℝ) :
    σ^2/(μ^2*(anchorRadius Lf Lg k E ε)^2) ≤
      σ^2/(μ^2*(lowerRadius Lg E ε)^2) +
        4096*(1+k)^2*Lf^2*σ^2/(μ^2*ε^2) := by
  have hh := mul_le_mul_of_nonneg_left (inverse_anchor_sq Lf Lg k E ε)
    (by positivity : 0 ≤ σ^2/μ^2)
  convert hh using 1 <;> ring

theorem lower_variance_identity (Lg E ε μ σ : ℝ) :
    σ^2/(μ^2*(lowerRadius Lg E ε)^2) =
      4096*(Lg/μ)^2*σ^2/(ε^2*(tilt E ε)^2) := by
  unfold lowerRadius
  simp only [div_pow, mul_pow, div_div_eq_mul_div]
  ring_nf
  simp only [inv_inv]
  ring

theorem upper_variance_identity (k ε σ : ℝ) :
    σ^2/(upperRadius k ε)^2 = 4096*(1+k)^2*σ^2/ε^2 := by
  unfold upperRadius
  simp only [div_pow, mul_pow, div_div_eq_mul_div]
  ring

theorem gradient_variance_identity (E ε σ : ℝ) :
    σ^2/(gradientRadius E ε)^2 = 4096*σ^2/(ε^2*(tilt E ε)^2) := by
  unfold gradientRadius
  simp only [div_pow, mul_pow, div_div_eq_mul_div]
  ring

end Bilevel.CachedParameterChoice
