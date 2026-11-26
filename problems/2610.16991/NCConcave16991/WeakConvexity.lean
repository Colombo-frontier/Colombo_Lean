import NCConcave16991.Moreau
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # A Lipschitz gradient implies weak convexity -/

open Set
open scoped InnerProductSpace

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem weaklyConvex_of_lipschitz_gradient {f : E → ℝ} {G : E → E} {L : ℝ}
    (hL : 0 ≤ L) (hf : ∀ x, HasGradientAt f (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) : WeaklyConvex L f := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let v := y - x
  let z := fun t : ℝ ↦ x + t • v
  let H := fun t : ℝ ↦ f (z t) + L / 2 * ‖z t‖ ^ 2
  let D := fun t : ℝ ↦ ⟪G (z t), v⟫_ℝ + L * ⟪z t, v⟫_ℝ
  have hz : ∀ t, HasDerivAt z v t := by
    intro t
    simpa only [z, id_eq, one_smul] using
      (((hasDerivAt_id t).smul_const v).const_add x)
  have hD : ∀ t, HasDerivAt H (D t) t := by
    intro t
    have hdf := (hf (z t)).hasFDerivAt.comp_hasDerivAt t (hz t)
    have hdn := (hz t).norm_sq
    have hh := hdf.add (hdn.const_mul (L / 2))
    convert hh using 1
    all_goals first
      | (ext u; rfl)
      | (dsimp [D]; ring)
  have hmono : Monotone D := by
    intro t s hts
    have hst : 0 ≤ s - t := sub_nonneg.mpr hts
    have hzt : z s - z t = (s - t) • v := by dsimp [z]; module
    have hnorm : ‖z s - z t‖ = (s - t) * ‖v‖ := by
      rw [hzt, norm_smul, Real.norm_eq_abs, abs_of_nonneg hst]
    have hgrad := hG (z s) (z t)
    rw [hnorm] at hgrad
    have hip : -‖G (z s) - G (z t)‖ * ‖v‖ ≤ ⟪G (z s) - G (z t), v⟫_ℝ := by
      have hh := real_inner_le_norm (-(G (z s) - G (z t))) v
      simp only [inner_neg_left, norm_neg] at hh
      linarith
    have hinner : ⟪z s, v⟫_ℝ - ⟪z t, v⟫_ℝ = (s - t) * ‖v‖ ^ 2 := by
      rw [← inner_sub_left, hzt, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hmul := mul_le_mul_of_nonneg_right hgrad (norm_nonneg v)
    dsimp [D]
    rw [inner_sub_left] at hip
    nlinarith
  have hconv : ConvexOn ℝ univ H :=
    (show Monotone (deriv H) by simpa only [funext (fun t ↦ (hD t).deriv)] using hmono).convexOn_univ_of_deriv
      (fun t ↦ (hD t).differentiableAt)
  have hh := hconv.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  have hz0 : z 0 = x := by simp [z]
  have hz1 : z 1 = y := by dsimp [z, v]; module
  have hzb : z b = a • x + b • y := by
    dsimp [z, v]
    rw [show a = 1 - b by linarith]
    module
  simpa only [H, smul_eq_mul, mul_zero, mul_one, zero_add, hz0, hz1, hzb] using hh

end NCConcave16991
