import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Integrating an actual Hessian lower bound gives the global strong-convexity model. -/

noncomputable section
namespace Bilevel.HessianLowerBound

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem first_order_lower {f : E → ℝ} {g : E → E} {H : E → E →L[ℝ] E} {m : ℝ}
    (hf : ∀ y, HasGradientAt f (g y) y)
    (hg : ∀ y, HasFDerivAt g (H y) y)
    (hH : ∀ y v, m * ‖v‖ ^ 2 ≤ ⟪H y v, v⟫) (u v : E) :
    f u + ⟪g u, v - u⟫ + m / 2 * ‖v - u‖ ^ 2 ≤ f v := by
  let d := v - u
  let a : ℝ → E := fun t => u + t • d
  let h : ℝ → ℝ := fun t => f (a t) - m / 2 * t ^ 2 * ‖d‖ ^ 2
  let b : ℝ → ℝ := fun t => ⟪g (a t), d⟫ - m * t * ‖d‖ ^ 2
  have ha (t : ℝ) : HasDerivAt a d t := by
    simpa [a] using ((hasDerivAt_id t).smul_const d).const_add u
  have hh (t : ℝ) : HasDerivAt h (b t) t := by
    have hfa := (hf (a t)).hasFDerivAt.comp_hasDerivAt t (ha t)
    have hc := (((hasDerivAt_pow 2 t).const_mul (m / 2)).mul_const (‖d‖ ^ 2))
    convert hfa.sub hc using 1
    simp [b, InnerProductSpace.toDual_apply, real_inner_comm]
    ring
    simp
  have hb (t : ℝ) : HasDerivAt b (⟪H (a t) d, d⟫ - m * ‖d‖ ^ 2) t := by
    have hga := (hg (a t)).comp_hasDerivAt t (ha t)
    have hin := hga.inner ℝ (hasDerivAt_const t d)
    have hc := ((hasDerivAt_id t).const_mul m).mul_const (‖d‖ ^ 2)
    convert hin.sub hc using 1
    simp
  have hm : Monotone b := monotone_of_deriv_nonneg (fun t => (hb t).differentiableAt)
    (fun t => by rw [(hb t).deriv]; exact sub_nonneg.mpr (hH (a t) d))
  have hderiv : deriv h = b := funext (fun t => (hh t).deriv)
  have hconv : ConvexOn ℝ Set.univ h :=
    Monotone.convexOn_univ_of_deriv (fun t => (hh t).differentiableAt) (hderiv.symm ▸ hm)
  have hsec := hconv.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) (by norm_num) (hh 0)
  simp only [b, h, a, zero_smul, add_zero, mul_zero, sub_zero, one_smul, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, one_pow, mul_one, d, add_sub_cancel,
    slope_def_field, sub_zero, one_div, inv_one] at hsec
  linarith

end Bilevel.HessianLowerBound
