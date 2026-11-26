import NoisyZO.SGDTelescope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# One projected biased-gradient step

This is the Hilbert-space algebra preceding the conditional-expectation
recurrence in Appendix D.  The later stochastic module only has to integrate
this pointwise inequality and use the conditional bias/second-moment bounds.
-/

open scoped InnerProductSpace

namespace NoisyZO

theorem biased_gradient_inner_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (grad g : E) (displacement : E) (gap B : ℝ)
    (hstrong : gap + (1 / 2 : ℝ) * ‖displacement‖ ^ 2 ≤
      ⟪grad, displacement⟫_ℝ)
    (hbias : ‖g - grad‖ ≤ B) :
    gap + (1 / 4 : ℝ) * ‖displacement‖ ^ 2 - B ^ 2 ≤
      ⟪g, displacement⟫_ℝ := by
  have hdecomp : g = grad + (g - grad) := by abel
  have hcauchy :
      -B * ‖displacement‖ ≤ ⟪g - grad, displacement⟫_ℝ := by
    have habs := abs_real_inner_le_norm (g - grad) displacement
    have hnorm : ‖g - grad‖ * ‖displacement‖ ≤ B * ‖displacement‖ := by
      gcongr
    calc
      -B * ‖displacement‖ ≤ -(‖g - grad‖ * ‖displacement‖) := by linarith
      _ ≤ -|⟪g - grad, displacement⟫_ℝ| := by linarith
      _ ≤ ⟪g - grad, displacement⟫_ℝ := neg_abs_le _
  have hyoung :
      B * ‖displacement‖ ≤
        (1 / 4 : ℝ) * ‖displacement‖ ^ 2 + B ^ 2 := by
    nlinarith [sq_nonneg (‖displacement‖ / 2 - B)]
  rw [hdecomp, inner_add_left]
  linarith

/-- Pointwise projected-step recurrence. -/
theorem projected_biased_gradient_step
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x xstar xnext grad g : E) (η gap B : ℝ)
    (hη : 0 ≤ η)
    (hprojection : ‖xnext - xstar‖ ≤ ‖(x - η • g) - xstar‖)
    (hstrong : gap + (1 / 2 : ℝ) * ‖x - xstar‖ ^ 2 ≤
      ⟪grad, x - xstar⟫_ℝ)
    (hbias : ‖g - grad‖ ≤ B) :
    ‖xnext - xstar‖ ^ 2 ≤
      (1 - η / 2) * ‖x - xstar‖ ^ 2 - 2 * η * gap +
        2 * η * B ^ 2 + η ^ 2 * ‖g‖ ^ 2 := by
  have hproj_sq :
      ‖xnext - xstar‖ ^ 2 ≤ ‖(x - η • g) - xstar‖ ^ 2 := by
    nlinarith [norm_nonneg (xnext - xstar), norm_nonneg ((x - η • g) - xstar)]
  have hrewrite : (x - η • g) - xstar = (x - xstar) - η • g := by abel
  have hinner_smul : ⟪x - xstar, η • g⟫_ℝ = η * ⟪g, x - xstar⟫_ℝ := by
    rw [real_inner_smul_right, real_inner_comm]
  have hstepnorm :
      ‖(x - xstar) - η • g‖ ^ 2 =
        ‖x - xstar‖ ^ 2 - 2 * η * ⟪g, x - xstar⟫_ℝ +
          η ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_sub_sq_real, hinner_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hη]
    ring
  rw [hrewrite, hstepnorm] at hproj_sq
  have hinner := biased_gradient_inner_lower grad g (x - xstar) gap B hstrong hbias
  nlinarith [sq_nonneg η, sq_nonneg ‖g‖]

end NoisyZO
