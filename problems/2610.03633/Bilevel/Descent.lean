import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Smooth-model descent and finite telescoping

The smooth quadratic upper model is an explicit hypothesis. The results below
prove the inner-product-space descent calculation in Appendix B and the finite
telescoping argument, including a zero-query gap threshold. They do not assert
the construction of a stochastic estimator or its conditional MSE guarantee.
-/

namespace Bilevel.Descent

open scoped BigOperators RealInnerProductSpace

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact completion of squares underlying inexact gradient descent. -/
theorem descent_identity (g G : E) (L : ℝ) (hL : 0 < L) :
    ⟪g, -(L⁻¹ • G)⟫ + L / 2 * ‖-(L⁻¹ • G)‖ ^ 2 =
      -‖g‖ ^ 2 / (2 * L) + ‖G - g‖ ^ 2 / (2 * L) := by
  rw [inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), norm_sub_sq_real,
    real_inner_comm G g]
  field_simp
  ring

/-- A smooth quadratic upper model implies the article's inexact descent bound. -/
theorem inexact_descent (F : E → ℝ) (x g G : E) (L : ℝ) (hL : 0 < L)
    (hmodel : ∀ h : E, F (x + h) ≤ F x + ⟪g, h⟫ + L / 2 * ‖h‖ ^ 2) :
    F (x - L⁻¹ • G) ≤ F x - ‖g‖ ^ 2 / (2 * L) + ‖G - g‖ ^ 2 / (2 * L) := by
  have h := hmodel (-(L⁻¹ • G))
  rw [← sub_eq_add_neg] at h
  have hi := descent_identity g G L hL
  calc
    F (x - L⁻¹ • G) ≤ F x +
        (⟪g, -(L⁻¹ • G)⟫ + L / 2 * ‖-(L⁻¹ • G)‖ ^ 2) := by
      simpa only [add_assoc] using h
    _ = F x - ‖g‖ ^ 2 / (2 * L) + ‖G - g‖ ^ 2 / (2 * L) := by
      rw [hi]
      ring

/-- The squared gradient is bounded by twice smoothness times the global gap. -/
theorem gradient_sq_le_gap (F : E → ℝ) (x g : E) (L lower : ℝ) (hL : 0 < L)
    (hmodel : ∀ h : E, F (x + h) ≤ F x + ⟪g, h⟫ + L / 2 * ‖h‖ ^ 2)
    (hlower : ∀ y, lower ≤ F y) :
    ‖g‖ ^ 2 ≤ 2 * L * (F x - lower) := by
  have h := inexact_descent F x g g L hL hmodel
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at h
  have hd : ‖g‖ ^ 2 / (2 * L) ≤ F x - lower := by
    linarith [hlower (x - L⁻¹ • g)]
  have hpos : 0 < 2 * L := by positivity
  have hmul := (div_le_iff₀ hpos).mp hd
  nlinarith

/-- If the initial gap is below `epsilon^2/(2 L)`, no query is necessary. -/
theorem zero_query_threshold (F : E → ℝ) (x g : E) (L lower ε : ℝ)
    (hL : 0 < L) (hε : 0 ≤ ε)
    (hmodel : ∀ h : E, F (x + h) ≤ F x + ⟪g, h⟫ + L / 2 * ‖h‖ ^ 2)
    (hlower : ∀ y, lower ≤ F y)
    (hgap : F x - lower ≤ ε ^ 2 / (2 * L)) :
    ‖g‖ ≤ ε := by
  have h := gradient_sq_le_gap F x g L lower hL hmodel hlower
  have hpos : 0 < 2 * L := by positivity
  have hgap' := (le_div_iff₀ hpos).mp hgap
  nlinarith [norm_nonneg g]

/-- A stationary point satisfying the strongly convex first-order model is a
global minimizer, and any point with no larger value must coincide with it. -/
theorem stationary_unique_minimizer (F : E → ℝ) (u gu : E) (μ : ℝ)
    (hμ : 0 < μ) (hzero : gu = 0)
    (hmodel : ∀ v : E, F u + ⟪gu, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v) :
    (∀ v, F u ≤ F v) ∧ (∀ v, F v ≤ F u → v = u) := by
  have hb : ∀ v : E, F u + μ / 2 * ‖v - u‖ ^ 2 ≤ F v := by
    intro v
    simpa only [hzero, inner_zero_left, add_zero] using hmodel v
  constructor
  · intro v
    have hs := sq_nonneg ‖v - u‖
    nlinarith [hb v]
  · intro v hv
    have hs := sq_nonneg ‖v - u‖
    have hterm : μ / 2 * ‖v - u‖ ^ 2 ≤ μ / 2 * 0 := by linarith [hb v]
    have hpos : 0 < μ / 2 := by positivity
    have hsle : ‖v - u‖ ^ 2 ≤ 0 := (mul_le_mul_left hpos).mp hterm
    have hz : ‖v - u‖ = 0 := by nlinarith [norm_nonneg (v - u)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end InnerProduct

/-- Finite deterministic telescoping, with an arbitrary nonnegative-step scale.
No sign hypothesis on the error sequence is necessary for this implication. -/
theorem finite_telescoping (value gradSq errorSq : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hstep : ∀ k < n, gradSq k ≤ c * (value k - value (k + 1)) + errorSq k) :
    (∑ k ∈ Finset.range n, gradSq k) ≤
      c * (value 0 - value n) + ∑ k ∈ Finset.range n, errorSq k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    have hn := hstep n (Nat.lt_succ_self n)
    simp only [Finset.sum_range_succ]
    nlinarith

/-- A finite gap and one-step descent bound control the sum of squared gradients.
The sequences can later be instantiated with expectations once integrability
and conditional-expectation facts have been proved separately. -/
theorem sum_gradient_sq_bound (value gradSq errorSq : ℕ → ℝ) (L Δ : ℝ)
    (n : ℕ) (hL : 0 < L) (hgap : value 0 - value n ≤ Δ)
    (hstep : ∀ k < n, value (k + 1) ≤
      value k - gradSq k / (2 * L) + errorSq k / (2 * L)) :
    (∑ k ∈ Finset.range n, gradSq k) ≤
      2 * L * Δ + ∑ k ∈ Finset.range n, errorSq k := by
  have hpos : 0 < 2 * L := by positivity
  have hscaled : ∀ k < n,
      gradSq k ≤ (2 * L) * (value k - value (k + 1)) + errorSq k := by
    intro k hk
    have h := mul_le_mul_of_nonneg_left (hstep k hk) (le_of_lt hpos)
    have heq : (2 * L) *
        (value k - gradSq k / (2 * L) + errorSq k / (2 * L)) =
        (2 * L) * value k - gradSq k + errorSq k := by
      field_simp
      ring
    rw [heq] at h
    nlinarith
  have ht := finite_telescoping value gradSq errorSq (2 * L) n hscaled
  have hg := mul_le_mul_of_nonneg_left hgap (le_of_lt hpos)
  linarith

/-- Averaged squared-gradient bound for a positive finite horizon. -/
theorem averaged_gradient_sq_bound (value gradSq errorSq : ℕ → ℝ)
    (L Δ : ℝ) (n : ℕ) (hn : 0 < n) (hL : 0 < L)
    (hgap : value 0 - value n ≤ Δ)
    (hstep : ∀ k < n, value (k + 1) ≤
      value k - gradSq k / (2 * L) + errorSq k / (2 * L)) :
    (∑ k ∈ Finset.range n, gradSq k) / (n : ℝ) ≤
      2 * L * Δ / n + (∑ k ∈ Finset.range n, errorSq k) / n := by
  have hn' : 0 ≤ (n : ℝ) := by positivity
  have h := div_le_div_of_nonneg_right
    (sum_gradient_sq_bound value gradSq errorSq L Δ n hL hgap hstep) hn'
  simpa only [add_div] using h

/-- Uniform per-step squared errors yield the familiar iteration/MSE tradeoff. -/
theorem averaged_gradient_sq_of_uniform_error (value gradSq errorSq : ℕ → ℝ)
    (L Δ δ : ℝ) (n : ℕ) (hn : 0 < n) (hL : 0 < L)
    (hgap : value 0 - value n ≤ Δ)
    (hstep : ∀ k < n, value (k + 1) ≤
      value k - gradSq k / (2 * L) + errorSq k / (2 * L))
    (herror : ∀ k < n, errorSq k ≤ δ) :
    (∑ k ∈ Finset.range n, gradSq k) / (n : ℝ) ≤ 2 * L * Δ / n + δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : (∑ k ∈ Finset.range n, errorSq k) ≤ (n : ℝ) * δ := by
    calc
      (∑ k ∈ Finset.range n, errorSq k) ≤ ∑ _k ∈ Finset.range n, δ := by
        apply Finset.sum_le_sum
        intro k hk
        exact herror k (Finset.mem_range.mp hk)
      _ = (n : ℝ) * δ := by simp
  have hd : (∑ k ∈ Finset.range n, errorSq k) / (n : ℝ) ≤ δ := by
    exact (div_le_iff₀ hn').mpr (by nlinarith [hs])
  have h := averaged_gradient_sq_bound value gradSq errorSq L Δ n hn hL hgap hstep
  linarith

end Bilevel.Descent
