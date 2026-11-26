import Bilevel.OuterDescent

/-!
# Sharp lower-solve contraction

The factor `1 - μ η` is derived from actual strong convexity and gradient
Lipschitzness, using the gradient-gap bound. It is not a separately assumed
cocoercivity certificate. Both the original and linearly tilted lower
problems instantiate the result.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace Bilevel.InnerContraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem smooth_upper_model (F : E → ℝ) (g : E → E) (L : ℝ)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖) (y d : E) :
    F (y + d) ≤ F y + ⟪g y, d⟫ + L / 2 * ‖d‖ ^ 2 := by
  have h := JointDerivative.gradient_taylor F g L hg hlip y d
  have he := (le_abs_self (F (y + d) - F y - ⟪g y, d⟫)).trans
    (by simpa only [Real.norm_eq_abs] using h)
  linarith

/-- The gradient-gap inequality uses the actual smooth lower objective. -/
theorem gradient_sq_le_suboptimality (F : E → ℝ) (g : E → E) {L : ℝ}
    (hL : 0 < L) (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (y ys : E) (hmin : ∀ z, F ys ≤ F z) :
    ‖g y‖ ^ 2 ≤ 2 * L * (F y - F ys) :=
  Descent.gradient_sq_le_gap F y (g y) L (F ys) hL
    (fun d => smooth_upper_model F g L hg hlip y d) hmin

/-- Combined strong-convexity and gradient-gap inequality. -/
theorem gradient_inner_lower (F : E → ℝ) (g : E → E) {L μ : ℝ}
    (hL : 0 < L) (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (y ys : E) (hmin : ∀ z, F ys ≤ F z) :
    μ / 2 * ‖y - ys‖ ^ 2 + ‖g y‖ ^ 2 / (2 * L) ≤ ⟪g y, y - ys⟫ := by
  have hgap := gradient_sq_le_suboptimality F g hL hg hlip y ys hmin
  have hd : ‖g y‖ ^ 2 / (2 * L) ≤ F y - F ys :=
    (div_le_iff₀ (by positivity : 0 < 2 * L)).mpr (by nlinarith)
  have hs := hstrong y ys
  have hi : ⟪g y, ys - y⟫ = -⟪g y, y - ys⟫ := by
    rw [inner_sub_right, inner_sub_right]
    ring
  rw [norm_sub_rev ys y, hi] at hs
  linarith

/-- The sharp `1 - μ η` squared-distance contraction for gradient descent. -/
theorem gradient_step_contraction (F : E → ℝ) (g : E → E) {L μ η : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η ≤ L⁻¹)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (y ys : E) (hmin : ∀ z, F ys ≤ F z) :
    ‖y - η • g y - ys‖ ^ 2 ≤ (1 - μ * η) * ‖y - ys‖ ^ 2 := by
  have hc := gradient_inner_lower F g hL hg hlip hstrong y ys hmin
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη)
  have heq : ‖y - η • g y - ys‖ ^ 2 =
      ‖y - ys‖ ^ 2 - 2 * η * ⟪g y, y - ys⟫ + η ^ 2 * ‖g y‖ ^ 2 := by
    have hid : y - η • g y - ys = (y - ys) - η • g y := by abel
    rw [hid, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hη, real_inner_comm (y - ys)]
    ring
  have he : 2 * η * (μ / 2 * ‖y - ys‖ ^ 2 + ‖g y‖ ^ 2 / (2 * L)) =
      μ * η * ‖y - ys‖ ^ 2 + η * L⁻¹ * ‖g y‖ ^ 2 := by ring
  rw [he] at hm
  rw [heq]
  calc
    ‖y - ys‖ ^ 2 - 2 * η * ⟪g y, y - ys⟫ + η ^ 2 * ‖g y‖ ^ 2 ≤
        (1 - μ * η) * ‖y - ys‖ ^ 2 + η * (η - L⁻¹) * ‖g y‖ ^ 2 := by nlinarith
    _ ≤ (1 - μ * η) * ‖y - ys‖ ^ 2 := by
      have hn := mul_nonpos_of_nonneg_of_nonpos hη (sub_nonpos.mpr hηL)
      have hn' := mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg ‖g y‖)
      linarith

/-- Pathwise noisy update bound; the cross term vanishes under conditionally
centered noise, giving the standard `η² σ²` stochastic contribution. -/
theorem noisy_step_bound (F : E → ℝ) (g : E → E) {L μ η : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η ≤ L⁻¹)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (y ys ξ : E) (hmin : ∀ z, F ys ≤ F z) :
    ‖y - η • (g y + ξ) - ys‖ ^ 2 ≤ (1 - μ * η) * ‖y - ys‖ ^ 2 -
      2 * η * ⟪y - η • g y - ys, ξ⟫ + η ^ 2 * ‖ξ‖ ^ 2 := by
  have h := gradient_step_contraction F g hL hη hηL hg hlip hstrong y ys hmin
  have hid : y - η • (g y + ξ) - ys = (y - η • g y - ys) - η • ξ := by
    rw [smul_add]
    abel
  rw [hid, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hη]
  nlinarith

end Bilevel.InnerContraction

namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

include P in
/-- In a nontrivial lower space the actual primitive constants satisfy `μ ≤ Lg`. -/
theorem strong_convexity_le_smoothness [Nontrivial Y] : μ ≤ Lg := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Y)
  have hp : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  have h := (P.lower_strong_monotone (0 : X) v 0).trans
    (real_inner_le_norm (P.gy 0 v - P.gy 0 0) (v - 0))
  have hn := P.gy_lipschitz_y (0 : X) v 0
  simp only [sub_zero] at h hn
  have hc := h.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg v))
  apply (mul_le_mul_right hp).mp
  nlinarith

/-- Actual lower-gradient descent has the condition-number-linear contraction. -/
theorem lower_gradient_step_contraction (x : X) (y ys : Y) {η : ℝ}
    (hLg : 0 < Lg) (hη : 0 ≤ η) (hηL : η ≤ Lg⁻¹) (hmin : P.IsLowerSolution x ys) :
    ‖y - η • P.gy x y - ys‖ ^ 2 ≤ (1 - μ * η) * ‖y - ys‖ ^ 2 :=
  InnerContraction.gradient_step_contraction (P.g x) (P.gy x) hLg hη hηL
    (P.has_gy x) (P.gy_lipschitz_y x) (P.strong_convex x) y ys hmin

/-- Freezing a linear tilt preserves both the smoothness and the contraction factor. -/
theorem tilted_gradient_step_contraction (x : X) (y ys a : Y) (t : ℝ) {η : ℝ}
    (hLg : 0 < Lg) (hη : 0 ≤ η) (hηL : η ≤ Lg⁻¹)
    (hmin : ∀ v, P.tiltedLower x t a ys ≤ P.tiltedLower x t a v) :
    ‖y - η • (P.gy x y + t • a) - ys‖ ^ 2 ≤ (1 - μ * η) * ‖y - ys‖ ^ 2 := by
  apply InnerContraction.gradient_step_contraction (P.tiltedLower x t a)
    (fun v => P.gy x v + t • a) hLg hη hηL
    (P.tilted_hasGradientAt x t a) _ (P.tilted_strong_convex x t a) y ys hmin
  intro u v
  simpa only [add_sub_add_right_eq_sub] using P.gy_lipschitz_y x u v

/-- Noise separated from deterministic contraction for an original lower solve. -/
theorem lower_noisy_step_bound (x : X) (y ys ξ : Y) {η : ℝ}
    (hLg : 0 < Lg) (hη : 0 ≤ η) (hηL : η ≤ Lg⁻¹) (hmin : P.IsLowerSolution x ys) :
    ‖y - η • (P.gy x y + ξ) - ys‖ ^ 2 ≤ (1 - μ * η) * ‖y - ys‖ ^ 2 -
      2 * η * ⟪y - η • P.gy x y - ys, ξ⟫ + η ^ 2 * ‖ξ‖ ^ 2 :=
  InnerContraction.noisy_step_bound (P.g x) (P.gy x) hLg hη hηL
    (P.has_gy x) (P.gy_lipschitz_y x) (P.strong_convex x) y ys ξ hmin

variable [FiniteDimensional ℝ Y]

theorem canonical_lower_gradient_step_contraction (x : X) (y : Y) {η : ℝ}
    (hLg : 0 < Lg) (hη : 0 ≤ η) (hηL : η ≤ Lg⁻¹) :
    ‖y - η • P.gy x y - P.canonicalResponse.y x‖ ^ 2 ≤
      (1 - μ * η) * ‖y - P.canonicalResponse.y x‖ ^ 2 :=
  P.lower_gradient_step_contraction x y (P.canonicalResponse.y x) hLg hη hηL
    (P.canonicalResponse.minimizes x)

theorem canonical_tilted_gradient_step_contraction (x : X) (y a : Y) (t : ℝ) {η : ℝ}
    (hLg : 0 < Lg) (hη : 0 ≤ η) (hηL : η ≤ Lg⁻¹) :
    ‖y - η • (P.gy x y + t • a) - P.tiltedResponse x t a‖ ^ 2 ≤
      (1 - μ * η) * ‖y - P.tiltedResponse x t a‖ ^ 2 :=
  P.tilted_gradient_step_contraction x y (P.tiltedResponse x t a) a t hLg hη hηL
    (P.tiltedResponse_minimizes x t a)

end Bilevel.Model.Primitive
