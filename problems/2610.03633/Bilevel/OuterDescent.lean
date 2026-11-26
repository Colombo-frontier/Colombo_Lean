import Bilevel.Curvature
import Bilevel.Descent

/-!
# Actual outer descent from primitive regularity

The smooth upper model and deterministic inexact descent are derived for the
composed hyperobjective. A positive step-size denominator may be any majorant
of the universal curvature coefficient; this also covers zero curvature by
choosing a positive majorant. Stochastic estimator construction and expectation
arguments are not asserted by these deterministic results.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators

namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

/-- The article's smooth quadratic upper model, proved for the actual objective. -/
theorem hyperobjective_upper_model (r : P.Response) (x d : X) :
    P.hyperobjective r (x + d) ≤ P.hyperobjective r x +
      ⟪gradient (P.hyperobjective r) x, d⟫ +
        ((1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ)) / 2 * ‖d‖ ^ 2 := by
  have hg : ∀ z, HasGradientAt (P.hyperobjective r) (gradient (P.hyperobjective r) z) z := by
    intro z
    rw [P.gradient_hyperobjective r z]
    exact P.hasGradient_hyperobjective r z
  have h := JointDerivative.gradient_taylor (P.hyperobjective r) (gradient (P.hyperobjective r))
    ((1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ)) hg
    (P.gradient_hyperobjective_norm_sub_le r) x d
  have he := (le_abs_self (P.hyperobjective r (x + d) - P.hyperobjective r x -
    ⟪gradient (P.hyperobjective r) x, d⟫)).trans (by simpa only [Real.norm_eq_abs] using h)
  linarith

/-- The same upper model for any prescribed curvature majorant. -/
theorem hyperobjective_upper_model_majorant (r : P.Response) (x d : X) (Λ : ℝ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ) :
    P.hyperobjective r (x + d) ≤ P.hyperobjective r x +
      ⟪gradient (P.hyperobjective r) x, d⟫ + Λ / 2 * ‖d‖ ^ 2 := by
  have h := P.hyperobjective_upper_model r x d
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hΛ (by norm_num)) (sq_nonneg _)) _)

/-- Appendix B's inexact descent inequality, now with no smooth-model assumption. -/
theorem outer_inexact_descent (r : P.Response) (x G : X) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ) :
    P.hyperobjective r (x - Λ⁻¹ • G) ≤ P.hyperobjective r x -
      ‖gradient (P.hyperobjective r) x‖ ^ 2 / (2 * Λ) +
      ‖G - gradient (P.hyperobjective r) x‖ ^ 2 / (2 * Λ) :=
  Descent.inexact_descent (P.hyperobjective r) x (gradient (P.hyperobjective r) x)
    G Λ hΛpos (fun d => P.hyperobjective_upper_model_majorant r x d Λ hΛ)

/-- A certified initial gap bounds the actual squared hypergradient. -/
theorem initial_gradient_sq_bound (r : P.Response) (x₀ : X) {Δ : ℝ}
    (gap : P.GapCertificate r x₀ Δ) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ) :
    ‖gradient (P.hyperobjective r) x₀‖ ^ 2 ≤ 2 * Λ * Δ := by
  have h := Descent.gradient_sq_le_gap (P.hyperobjective r) x₀
    (gradient (P.hyperobjective r) x₀) Λ gap.floor hΛpos
    (fun d => P.hyperobjective_upper_model_majorant r x₀ d Λ hΛ) gap.lower_bound
  exact h.trans (mul_le_mul_of_nonneg_left gap.gap (by positivity))

/-- The original initial point already meets the target below this gap threshold. -/
theorem initial_point_meets_target (r : P.Response) (x₀ : X) {Δ ε : ℝ}
    (gap : P.GapCertificate r x₀ Δ) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ)
    (hε : 0 ≤ ε) (hsmall : Δ ≤ ε ^ 2 / (2 * Λ)) :
    ‖gradient (P.hyperobjective r) x₀‖ ≤ ε :=
  Descent.zero_query_threshold (P.hyperobjective r) x₀
    (gradient (P.hyperobjective r) x₀) Λ gap.floor ε hΛpos hε
    (fun d => P.hyperobjective_upper_model_majorant r x₀ d Λ hΛ)
    gap.lower_bound (gap.gap.trans hsmall)

/-- Deterministic finite-horizon descent for actual outer iterates and errors. -/
theorem outer_average_gradient_bound (r : P.Response) (x G : ℕ → X) {Δ δ : ℝ}
    (gap : P.GapCertificate r (x 0) Δ) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hΛ : (1 + Lg / μ) ^ 2 * (Lf + ρ * Cf / μ) ≤ Λ)
    (n : ℕ) (hn : 0 < n)
    (hstep : ∀ k < n, x (k + 1) = x k - Λ⁻¹ • G k)
    (herror : ∀ k < n, ‖G k - gradient (P.hyperobjective r) (x k)‖ ^ 2 ≤ δ) :
    (∑ k ∈ Finset.range n, ‖gradient (P.hyperobjective r) (x k)‖ ^ 2) / (n : ℝ) ≤
      2 * Λ * Δ / n + δ := by
  apply Descent.averaged_gradient_sq_of_uniform_error
    (fun k => P.hyperobjective r (x k))
    (fun k => ‖gradient (P.hyperobjective r) (x k)‖ ^ 2)
    (fun k => ‖G k - gradient (P.hyperobjective r) (x k)‖ ^ 2)
    Λ Δ δ n hn hΛpos
  · linarith [gap.lower_bound (x n), gap.gap]
  · intro k hk
    rw [hstep k hk]
    exact P.outer_inexact_descent r (x k) (G k) Λ hΛpos hΛ
  · exact herror

end Bilevel.Model.Primitive
