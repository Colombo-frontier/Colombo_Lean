import FreshGradientMinimax.Basic

/-! Dimension-independent proximal reduction and saddle residual certificates.
Analytic supporting inequalities and existence/optimality of the proximal point
are supplied explicitly. No SCSC algorithm is assumed to exist implicitly. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def proximalValue (Φ : E → ℝ) (L : ℝ) (c x : E) : ℝ := Φ x + L * ‖x - c‖ ^ 2
def proximalResidual (L : ℝ) (c u : E) : E := (2 * L) • (c - u)

/-- Equation (9), using strong convexity of P at its minimizer. -/
theorem proximal_decrease {Φ : E → ℝ} {L : ℝ} (hL : 0 < L) (c u : E)
    (hsc : proximalValue Φ L c u + L / 2 * ‖c - u‖ ^ 2 ≤ proximalValue Φ L c c) :
    ‖proximalResidual L c u‖ ^ 2 / (8 * L) ≤
      Φ c - proximalValue Φ L c u := by
  have heq : ‖proximalResidual L c u‖ ^ 2 / (8 * L) = L / 2 * ‖c - u‖ ^ 2 := by
    rw [proximalResidual, norm_smul_sq]
    field_simp
    ring
  rw [heq]
  have hs : proximalValue Φ L c c = Φ c := by simp [proximalValue]
  rw [hs] at hsc
  linarith

/-- The one-step inequality in the proof of Theorem G.1. -/
theorem inexact_proximal_step {Φ : E → ℝ} {L η : ℝ} (hL : 0 < L) (c u x : E)
    (hsc : proximalValue Φ L c u + L / 2 * ‖c - u‖ ^ 2 ≤ proximalValue Φ L c c)
    (hgap : proximalValue Φ L c x ≤ proximalValue Φ L c u + η) :
    Φ x + L * ‖x - c‖ ^ 2 ≤
      Φ c - ‖proximalResidual L c u‖ ^ 2 / (8 * L) + η := by
  have hd := proximal_decrease hL c u hsc
  change Φ x + L * ‖x - c‖ ^ 2 ≤ _ at hgap
  linarith

/-- Equation (10), stated for the exact gradient of the regularized value. -/
theorem primal_gradient_identity {L : ℝ} (c u x gradΦ : E) :
    gradΦ = proximalResidual L c u + (gradΦ + (2 * L) • (x - c)) -
      (2 * L) • (x - u) := by
  unfold proximalResidual
  module

/-- The constant 18 used to convert the fine subproblem's gradient in G.1. -/
theorem true_gradient_sq_bound {L : ℝ} (hL : 0 ≤ L)
    (g m h d : E) (hidentity : g = m + h - (2 * L) • d)
    (hd : L * ‖d‖ ≤ ‖h‖) :
    ‖g‖ ^ 2 ≤ 2 * ‖m‖ ^ 2 + 18 * ‖h‖ ^ 2 := by
  have herr : ‖h - (2 * L) • d‖ ≤ 3 * ‖h‖ := by
    have ht := norm_sub_le h ((2 * L) • d)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * L)] at ht
    nlinarith
  have hsq : ‖h - (2 * L) • d‖ ^ 2 ≤ 9 * ‖h‖ ^ 2 := by
    nlinarith [norm_nonneg (h - (2 * L) • d), norm_nonneg h]
  rw [hidentity, add_sub_assoc]
  have ht := norm_add_sq_le_two m (h - (2 * L) • d)
  linarith

/-- Full finite telescoping with both descent terms retained, equation (53). -/
theorem sum_descent {N : ℕ} {f q w : ℕ → ℝ} {L η Δ : ℝ}
    (hstep : ∀ t < N, f (t + 1) + L * w t ≤ f t - q t / (8 * L) + η)
    (hgap : f 0 - f N ≤ Δ) :
    (∑ t ∈ Finset.range N, q t) / (8 * L) +
      L * (∑ t ∈ Finset.range N, w t) ≤ Δ + N * η := by
  have htel : ∀ n ≤ N,
      f n + (∑ t ∈ Finset.range n, q t) / (8 * L) +
        L * (∑ t ∈ Finset.range n, w t) ≤ f 0 + n * η := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hi := ih (by omega)
      have hs := hstep n (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, add_div]
      linarith
  have h := htel N le_rfl
  linarith

theorem average_residual_bound {N : ℕ} (hN : 0 < N) {q w : ℕ → ℝ} {L η Δ : ℝ}
    (hL : 0 < L) (hw : ∀ t < N, 0 ≤ w t)
    (htel : (∑ t ∈ Finset.range N, q t) / (8 * L) +
      L * (∑ t ∈ Finset.range N, w t) ≤ Δ + N * η) :
    (∑ t ∈ Finset.range N, q t) / N ≤ 8 * L * (Δ / N + η) := by
  have hw' : 0 ≤ ∑ t ∈ Finset.range N, w t :=
    Finset.sum_nonneg (fun t ht => hw t (Finset.mem_range.mp ht))
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : (∑ t ∈ Finset.range N, q t) / (8 * L) ≤ Δ + N * η := by
    nlinarith
  have hb' := (div_le_iff₀ (by positivity : 0 < 8 * L)).mp hb
  apply (div_le_iff₀ hn).mpr
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  have he : 8 * L * (Δ / N + η) * N = (Δ + N * η) * (8 * L) := by
    field_simp
    ring
  rwa [he]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The saddle-gap residual certificate, proved by completing two squares. -/
theorem saddle_gap_certificate {g : E → F → ℝ} {α μ : ℝ}
    (hα : 0 < α) (hμ : 0 < μ) (u z : E) (v w : F) (gu : E) (gv : F)
    (hconv : g u v + ⟪gu, z - u⟫_ℝ + α / 2 * ‖z - u‖ ^ 2 ≤ g z v)
    (hconc : g u w ≤ g u v + ⟪gv, w - v⟫_ℝ - μ / 2 * ‖w - v‖ ^ 2) :
    g u w - g z v ≤ ‖gu‖ ^ 2 / (2 * α) + ‖gv‖ ^ 2 / (2 * μ) := by
  have hu := inner_sub_quadratic_le hα (-gu) (z - u)
  have hv := inner_sub_quadratic_le hμ gv (w - v)
  simp only [inner_neg_left, norm_neg] at hu
  linarith

end FreshGradientMinimax
