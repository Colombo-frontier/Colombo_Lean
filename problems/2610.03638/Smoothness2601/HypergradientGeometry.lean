import Smoothness2601.AdjointGeometry

/-! Source C_y and the error decomposition at arbitrary approximate lower
and adjoint solutions, for the actual composed Population objective. -/
noncomputable section
namespace Smoothness2601.HypergradientGeometry
open Bilevel.Model
open AdjointGeometry

def innerSensitivity (b : Budgets) : ℝ :=
  (1+b.L₁/b.μ)*(b.L₁+b.L₂*b.L₀/b.μ)

def outerSmoothness (b : Budgets) : ℝ :=
  Real.sqrt (1+(b.L₁/b.μ) ^ 2)*innerSensitivity b

theorem innerSensitivity_pos (b : Budgets) : 0 < innerSensitivity b := by
  have := b.L₁_pos
  have := b.μ_pos
  have := b.L₂_pos
  have := b.L₀_pos
  unfold innerSensitivity
  positivity

theorem innerSensitivity_source (b : Budgets) : innerSensitivity b =
    b.L₁+b.L₂*b.L₀/b.μ+b.L₁*b.L₂*b.L₀/b.μ ^ 2+b.L₁ ^ 2/b.μ := by
  unfold innerSensitivity
  ring

theorem outerSmoothness_pos (b : Budgets) : 0 < outerSmoothness b := by
  have hi := innerSensitivity_pos b
  unfold outerSmoothness
  positivity

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {b : Budgets}
  (P : Population (X := X) (Y := Y) b)

def surrogate (x : X) (y : Y) : X := P.primitive.fx x y-P.gxy x y (target P (x,y))

theorem surrogate_joint (x x' : X) (y y' : Y) :
    ‖surrogate P x y-surrogate P x' y'‖ ≤ innerSensitivity b*jointDistance x x' y y' := by
  have hu := P.primitive.upper_component_bounds x x' y y'
  exact Bilevel.Curvature.hypergradient_difference (P.primitive.fx x y) (P.primitive.fx x' y')
    (P.primitive.fy x y) (P.primitive.fy x' y') (P.gxy x y) (P.gxy x' y')
    (P.gyy x y) (P.gyy x' y') (P.primitive.inverseAt x y) (P.primitive.inverseAt x' y')
    (P.primitive.inverseAt_left x y) (P.primitive.inverseAt_right x' y')
    b.μ_pos b.L₁_pos.le b.L₂_pos.le (Real.sqrt_nonneg _)
    (P.primitive.inverseAt_norm x y) (P.primitive.inverseAt_norm x' y')
    (P.primitive.mixed_hessian_norm x y) (P.primitive.mixed_hessian_norm x' y')
    (P.primitive.variation_xy x x' y y') (P.primitive.variation_yy x x' y y')
    hu.1 hu.2 (P.primitive.upper_bound x' y')

theorem surrogate_y (x : X) (y y' : Y) :
    ‖surrogate P x y-surrogate P x y'‖ ≤ innerSensitivity b*‖y-y'‖ := by
  simpa [jointDistance] using surrogate_joint P x x y y'

theorem gradient_eq_surrogate (x : X) : gradient P.objective x = surrogate P x (P.yStar x) :=
  P.actual_hypergradient x

theorem surrogate_error (x : X) (y : Y) :
    ‖surrogate P x y-gradient P.objective x‖ ≤ innerSensitivity b*‖y-P.yStar x‖ := by
  rw [gradient_eq_surrogate]
  exact surrogate_y P x y (P.yStar x)

theorem outer_smoothness (x z : X) :
    ‖gradient P.objective x-gradient P.objective z‖ ≤ outerSmoothness b*‖x-z‖ := by
  have hr := P.primitive.response_distance_bound P.primitive.canonicalResponse x z
  have hκ : 0 ≤ b.L₁/b.μ := div_nonneg b.L₁_pos.le b.μ_pos.le
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hκ (norm_nonneg _))).mpr hr
  change ‖P.yStar x-P.yStar z‖ ^ 2 ≤ (b.L₁/b.μ*‖x-z‖) ^ 2 at hr2
  have hd : jointDistance x z (P.yStar x) (P.yStar z) ≤
      Real.sqrt (1+(b.L₁/b.μ) ^ 2)*‖x-z‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity),mul_pow,Real.sq_sqrt (by positivity)]
    nlinarith
  rw [gradient_eq_surrogate,gradient_eq_surrogate]
  exact (surrogate_joint P x z (P.yStar x) (P.yStar z)).trans
    ((mul_le_mul_of_nonneg_left hd (innerSensitivity_pos b).le).trans_eq (by unfold outerSmoothness; ring))

theorem adjoint_error (x : X) (y v : Y) :
    ‖(P.primitive.fx x y-P.gxy x y (Bilevel.Clipping.clip (ballRadius b) v))-surrogate P x y‖ ≤
      b.L₁*‖v-target P (x,y)‖ := by
  have he : (P.primitive.fx x y-P.gxy x y (Bilevel.Clipping.clip (ballRadius b) v))-surrogate P x y =
      -(P.gxy x y (Bilevel.Clipping.clip (ballRadius b) v-target P (x,y))) := by
    unfold surrogate
    rw [map_sub]
    abel
  rw [he,norm_neg]
  exact (((P.gxy x y).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (P.primitive.mixed_hessian_norm x y) (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_left (Bilevel.Clipping.error_nonincreasing _ (ballRadius_nonneg b)
      v (target P (x,y)) (target_in_ball P (x,y))) b.L₁_pos.le)

theorem biased_direction_error (x : X) (y v : Y) (m : X) {a : ℝ}
    (hbias : ‖m-P.gxy x y (Bilevel.Clipping.clip (ballRadius b) v)‖ ≤ a) :
    ‖(P.primitive.fx x y-m)-gradient P.objective x‖ ≤
      a+b.L₁*‖v-target P (x,y)‖+innerSensitivity b*‖y-P.yStar x‖ := by
  have hb : ‖(P.primitive.fx x y-m)-
      (P.primitive.fx x y-P.gxy x y (Bilevel.Clipping.clip (ballRadius b) v))‖ ≤ a := by
    simpa only [sub_sub_sub_cancel_left,norm_sub_rev] using hbias
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (P.primitive.fx x y-m)
    (P.primitive.fx x y-P.gxy x y (Bilevel.Clipping.clip (ballRadius b) v)) (surrogate P x y)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (P.primitive.fx x y-m)
    (surrogate P x y) (gradient P.objective x)
  exact h₂.trans (add_le_add (h₁.trans (add_le_add hb (adjoint_error P x y v))) (surrogate_error P x y))

end Smoothness2601.HypergradientGeometry
