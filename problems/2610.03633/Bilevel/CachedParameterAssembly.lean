import Bilevel.CachedRefreshBudget

/-! The complete deterministic estimator budget after substituting the actual
public tolerance choices. Includes the zero upper-smoothness refresh branch. -/
noncomputable section
namespace Bilevel.CachedParameterChoice
open CachedBudgetCalibration

def anchorSmoothness (Lf k : ℝ) : ℝ := Lf*(1+k)^2

theorem anchorSmoothness_nonneg {Lf k : ℝ} (hLf : 0 ≤ Lf) :
    0 ≤ anchorSmoothness Lf k := mul_nonneg hLf (sq_nonneg _)

theorem estimator_error_budget {Lf Lg k E Λ Δ ε : ℝ}
    (hLf : 0 ≤ Lf) (hLg : 0 < Lg) (hk : 0 ≤ k) (hE : 0 ≤ E) (hε : 0 < ε) :
    (1+k)*(upperRadius k ε + Lf*anchorRadius Lf Lg k E ε +
      Lf*(1+k)*refreshRadius Λ (anchorSmoothness Lf k) Δ ε) +
      (tilt E ε)⁻¹ * (2*Lg*lowerRadius Lg E ε + 2*gradientRadius E ε) + E*tilt E ε ≤ ε/8 := by
  have hη := upper_budget (ε := ε) hk
  have hA := anchor_budget (Lg := Lg) (E := E) hLf hk hε
  have hx := refreshRadius_budget (Λ := Λ) (Δ := Δ) (anchorSmoothness_nonneg (k := k) hLf) hε
  have hB := bias_budget hE hε
  have ht := tilt_pos hE hε
  have hcache : (1+k)*(upperRadius k ε + Lf*anchorRadius Lf Lg k E ε +
      Lf*(1+k)*refreshRadius Λ (anchorSmoothness Lf k) Δ ε) ≤ 3*ε/64 := by
    change Lf*(1+k)^2*refreshRadius Λ (anchorSmoothness Lf k) Δ ε ≤ ε/64 at hx
    nlinarith
  have hinner : (tilt E ε)⁻¹ *
      (2*Lg*lowerRadius Lg E ε + 2*gradientRadius E ε) = ε/16 := by
    rw [show 2*Lg*lowerRadius Lg E ε = 2*(Lg*lowerRadius Lg E ε) by ring,
      lower_budget hLg]
    unfold gradientRadius
    field_simp
    ring
  rw [hinner]
  linarith

end Bilevel.CachedParameterChoice
