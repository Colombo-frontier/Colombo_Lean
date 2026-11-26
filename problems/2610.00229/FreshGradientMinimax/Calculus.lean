import FreshGradientMinimax.Basic
import Mathlib.Analysis.Convex.Deriv

/-! Sharp smooth Taylor remainder, adapted to arbitrary real inner product
spaces from the already checked calculus argument in the sibling project
StronglyConvexValue/ExactValue/SmoothModel.lean. This file depends only on mathlib. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem scalar_derivative_comparison {f g df dg : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hg : ∀ t, HasDerivAt g (dg t) t)
    (hle : ∀ t ∈ Set.Icc (0 : ℝ) 1, df t ≤ dg t) : f 1 - f 0 ≤ g 1 - g 0 := by
  have hd (t : ℝ) := (hg t).sub (hf t)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    (show ContinuousOn (fun t => g t - f t) (Set.Icc 0 1) from
      (show Continuous (fun t => g t - f t) from continuous_iff_continuousAt.mpr
        (fun t => (hd t).continuousAt)).continuousOn)
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t ht => sub_nonneg.mpr (hle t (interior_subset ht)))
  have h := hm (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
    (show (0 : ℝ) ≤ 1 by norm_num)
  dsimp only at h
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem along_line_hasDerivAt {f : E → ℝ} {G : E → E}
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) (y h : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (y + t • h)) ⟪G (y + t • h), h⟫_ℝ t := by
  simpa only [id_eq, one_smul] using
    (hder _).comp_hasDerivAt t (((hasDerivAt_id t).smul_const h).const_add y)

theorem smooth_taylor_remainder {f : E → ℝ} {G : E → E} {L : ℝ}
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (y h : E) :
    |f (y + h) - f y - ⟪G y, h⟫_ℝ| ≤ L / 2 * ‖h‖ ^ 2 := by
  let φ := fun t : ℝ => f (y + t • h) - f y - t * ⟪G y, h⟫_ℝ
  let q := fun t : ℝ => L / 2 * t ^ 2 * ‖h‖ ^ 2
  have hφ (t : ℝ) : HasDerivAt φ ⟪G (y + t • h) - G y, h⟫_ℝ t := by
    convert ((along_line_hasDerivAt hder y h t).sub_const (f y)).sub
      ((hasDerivAt_id t).mul_const ⟪G y, h⟫_ℝ) using 1
    simp only [inner_sub_left, one_mul]
  have hq (t : ℝ) : HasDerivAt q (L * t * ‖h‖ ^ 2) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖h‖ ^ 2) using 1
    dsimp only [id_eq]
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      |⟪G (y + t • h) - G y, h⟫_ℝ| ≤ L * t * ‖h‖ ^ 2 := by
    have hi := abs_real_inner_le_norm (G (y + t • h) - G y) h
    have hl := hLip (y + t • h) y
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hl
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg h)
    nlinarith
  have hup := scalar_derivative_comparison hφ hq (fun t ht => (le_abs_self _).trans (hbound t ht))
  have hlo := scalar_derivative_comparison (fun t => (hφ t).neg) hq
    (fun t ht => (neg_le_abs _).trans (hbound t ht))
  simp only [φ, q, one_smul, zero_smul, add_zero, zero_mul, one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_one, one_mul, mul_zero, sub_self, sub_zero, neg_zero] at hup hlo
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- The actual gradient step decreases any function with an L-Lipschitz gradient. -/
theorem smooth_gradient_step {f : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x : E) :
    f (x - L⁻¹ • G x) ≤ f x - ‖G x‖ ^ 2 / (2 * L) := by
  have h := (abs_le.mp (smooth_taylor_remainder hder hLip x (-(L⁻¹ • G x)))).2
  have hi : ⟪G x, -(L⁻¹ • G x)⟫_ℝ = -L⁻¹ * ‖G x‖ ^ 2 := by
    simp [real_inner_self_eq_norm_sq, real_inner_smul_right]
  have hn : ‖-(L⁻¹ • G x)‖ ^ 2 = L⁻¹ ^ 2 * ‖G x‖ ^ 2 := by
    rw [norm_neg, norm_smul_sq]
  rw [hi, hn, ← sub_eq_add_neg] at h
  have he : L / 2 * (L⁻¹ ^ 2 * ‖G x‖ ^ 2) - L⁻¹ * ‖G x‖ ^ 2 =
      -‖G x‖ ^ 2 / (2 * L) := by field_simp; ring
  calc
    _ ≤ f x + (L / 2 * (L⁻¹ ^ 2 * ‖G x‖ ^ 2) - L⁻¹ * ‖G x‖ ^ 2) := by
      nlinarith only [h]
    _ = _ := by rw [he]; ring

/-- Gradient self-bounding uses a genuine global minimum. -/
theorem smooth_gradient_sq_le_gap {f : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (u : E) (hu : ∀ x, f u ≤ f x) (x : E) : ‖G x‖ ^ 2 ≤ 2 * L * (f x - f u) := by
  have h := smooth_gradient_step hL hder hLip x
  have hm := hu (x - L⁻¹ • G x)
  have hb : ‖G x‖ ^ 2 / (2 * L) ≤ f x - f u := by linarith
  have := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hb
  nlinarith

end FreshGradientMinimax
