import Bilevel.ZeroVariation
import Bilevel.SourcePrimitive
import Smoothness2601.Population

/-! Source Proposition `prop:decoupling`. The boundary conclusion is derived
from the population assumptions; none of its Hessian identities are assumed. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Smoothness2601
namespace Boundary

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Cf ρ : ℝ}
  (P : Bilevel.Model.Primitive (X := X) (Y := Y) μ Lf μ Cf ρ)

theorem lower_gradient_difference (x : X) (u v : Y) :
    P.gy x u - P.gy x v = μ • (u - v) := by
  have hs := P.smooth_g x x u v
  simp only [sub_self, norm_zero, sq, zero_mul, zero_add] at hs
  have hm := P.lower_strong_monotone x u v
  have hn := norm_sub_sq_real (P.gy x u - P.gy x v) (μ • (u - v))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos P.μ_pos,
    real_inner_smul_right] at hn
  have hz : ‖P.gy x u - P.gy x v - μ • (u - v)‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ‖P.gx x u - P.gx x v‖,
      mul_le_mul_of_nonneg_left hm P.μ_pos.le]
  have hn0 := norm_nonneg (P.gy x u - P.gy x v - μ • (u - v))
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith))

theorem upper_gradient_constant_in_lower (x : X) (u v : Y) :
    P.gx x u = P.gx x v := by
  have hs := P.smooth_g x x u v
  rw [lower_gradient_difference P x u v, norm_smul, Real.norm_eq_abs,
    abs_of_pos P.μ_pos] at hs
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hs
  have hn : ‖P.gx x u - P.gx x v‖ = 0 := by
    nlinarith [sq_nonneg ‖P.gx x u - P.gx x v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem mixed_hessian_zero (x : X) (y : Y) : P.gxy x y = 0 := by
  have he : P.gx x = fun _ => P.gx x 0 :=
    funext (fun u => upper_gradient_constant_in_lower P x u 0)
  have h := P.has_gxy x y
  rw [he] at h
  exact h.unique (hasFDerivAt_const (P.gx x 0) y)

theorem lower_hessian_scalar (x : X) (y : Y) :
    P.gyy x y = μ • ContinuousLinearMap.id ℝ Y := by
  have he : P.gy x = fun u => μ • u + P.gy x 0 := by
    funext u
    have h := lower_gradient_difference P x u 0
    simpa only [sub_zero] using eq_add_of_sub_eq h
  have h := P.has_gyy x y
  rw [he] at h
  exact h.unique (((hasFDerivAt_id y).const_smul μ).add_const _)

theorem lower_gradient_constant_in_upper (x z : X) (y : Y) :
    P.gy x y = P.gy z y := by
  have hd : ∀ w, HasFDerivAt (fun w => P.gy w y) (0 : X →L[ℝ] Y) w := by
    intro w
    simpa only [mixed_hessian_zero P w y, map_zero] using P.has_gyx w y
  exact is_const_of_fderiv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).fderiv) x z

theorem lower_gradient_affine (x : X) (y : Y) :
    P.gy x y = μ • y + P.gy 0 0 := by
  have h := lower_gradient_difference P x y 0
  rw [sub_zero, lower_gradient_constant_in_upper P x 0 0] at h
  exact eq_add_of_sub_eq h

theorem response_constant (r : P.Response) (x : X) :
    r.y x = (-μ⁻¹) • P.gy 0 0 := by
  have h := P.minimizer_stationary x (r.y x) (r.minimizes x)
  rw [lower_gradient_affine P] at h
  have he : μ • r.y x = -P.gy 0 0 := eq_neg_of_add_eq_zero_left h
  have he' := congrArg (fun v : Y => μ⁻¹ • v) he
  simpa only [smul_smul, inv_mul_cancel₀ P.μ_pos.ne', one_smul,
    smul_neg, neg_smul] using he'

/-- All identities asserted in the source proposition, for any lower response. -/
theorem forced_decoupling (r : P.Response) :
    (∀ x y, P.gyy x y = μ • ContinuousLinearMap.id ℝ Y) ∧
    (∀ x y, P.gxy x y = 0) ∧
    (∀ x y, P.gy x y = μ • y + P.gy 0 0) ∧
    (∀ x, r.y x = (-μ⁻¹) • P.gy 0 0) :=
  ⟨lower_hessian_scalar P, mixed_hessian_zero P, lower_gradient_affine P,
    response_constant P r⟩

/-- The source lower response exists, so the constant-response conclusion does
not require an unproved minimizer-existence hypothesis. -/
theorem canonical_response_constant [FiniteDimensional ℝ Y] (x : X) :
    P.canonicalResponse.y x = (-μ⁻¹) • P.gy 0 0 :=
  response_constant P P.canonicalResponse x

theorem decoupling_of_equal_budget {Lg : ℝ}
    (Q : Bilevel.Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
    (heq : Lg = μ) [FiniteDimensional ℝ Y] :
    (∀ x y, Q.gyy x y = μ • ContinuousLinearMap.id ℝ Y) ∧
    (∀ x y, Q.gxy x y = 0) ∧
    (∀ x y, Q.gy x y = μ • y + Q.gy 0 0) ∧
    (∀ x, Q.canonicalResponse.y x = (-μ⁻¹) • Q.gy 0 0) := by
  subst Lg
  exact forced_decoupling Q Q.canonicalResponse

/-- Proposition `prop:decoupling` directly from the source-facing population
model, including construction of its actual lower minimizer. -/
theorem source_forced_decoupling {b : Budgets}
    (Q : Population (X := X) (Y := Y) b) (heq : b.L₁ = b.μ)
    [FiniteDimensional ℝ Y] :
    (∀ x y, Q.gyy x y = b.μ • ContinuousLinearMap.id ℝ Y) ∧
    (∀ x y, Q.gxy x y = 0) ∧
    (∀ x y, (Q.grad_g (Bilevel.PrimitiveGeometry.pack x y)).snd =
      b.μ • y + (Q.grad_g (Bilevel.PrimitiveGeometry.pack 0 0)).snd) ∧
    (∀ x, Q.yStar x = (-b.μ⁻¹) • (Q.grad_g (Bilevel.PrimitiveGeometry.pack 0 0)).snd) :=
  decoupling_of_equal_budget Q.primitive heq

end Boundary
end Smoothness2601
