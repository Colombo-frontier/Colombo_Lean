import Bilevel.Model
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# From primitive regularity to the ideal frozen-tilt estimate

This module derives mixed-Hessian norm bounds, Hessian coercivity, inverse
norm bounds and the deterministic frozen-tilt estimate from `Model.Primitive`.
Existence of the lower response and tilted stationary point is supplied
explicitly. Hessian inverse existence is proved in finite dimension. The
identification of the hypergradient expression with the derivative of the
composed hyperobjective is not proved here.
-/

noncomputable section
open scoped RealInnerProductSpace Topology
open Filter

namespace Bilevel.FrozenTilt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Differentiating a strongly monotone map gives a coercive derivative. -/
theorem derivative_coercive {g : E → E} {μ : ℝ} (hg : StrongMonotone g μ)
    (y : E) (H : E →L[ℝ] E) (hH : HasFDerivAt g H y) (v : E) :
    μ * ‖v‖ ^ 2 ≤ ⟪H v, v⟫ := by
  let f : ℝ → ℝ := fun s => ⟪g (y + s • v) - g y, v⟫
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hgline : HasDerivAt (fun s : ℝ => g (y + s • v)) (H v) 0 := by
    exact (by simpa using hH : HasFDerivAt g H (y + (0 : ℝ) • v)).comp_hasDerivAt 0 hline
  have hf : HasDerivAt f ⟪H v, v⟫ 0 := by
    simpa [f] using (hgline.sub_const (g y)).inner ℝ (hasDerivAt_const (0 : ℝ) v)
  have hlim := hf.tendsto_slope_zero_right
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : 0 < s := hs
  have h := hg (y + s • v) y
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
    real_inner_smul_right] at h
  have hmul : s * (μ * s * ‖v‖ ^ 2) ≤ s * f s := by
    dsimp [f]
    nlinarith
  have hc : μ * s * ‖v‖ ^ 2 ≤ f s := (mul_le_mul_left hs).mp hmul
  have hd : μ * ‖v‖ ^ 2 ≤ f s / s := (le_div_iff₀ hs).mpr (by nlinarith)
  simpa [f, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd

end Bilevel.FrozenTilt

namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem gx_lipschitz_y (x : X) (u v : Y) :
    ‖P.gx x u - P.gx x v‖ ≤ Lg * ‖u - v‖ := by
  have h := P.smooth_g x x u v
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  have hsq : ‖P.gx x u - P.gx x v‖ ^ 2 ≤ (Lg * ‖u - v‖) ^ 2 := by
    nlinarith [sq_nonneg ‖P.gy x u - P.gy x v‖]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg P.Lg_nonneg (norm_nonneg _))).mp hsq

theorem mixed_hessian_norm (x : X) (y : Y) : ‖P.gxy x y‖ ≤ Lg := by
  exact (P.has_gxy x y).le_of_lip' P.Lg_nonneg
    (Filter.Eventually.of_forall (fun z => P.gx_lipschitz_y x z y))

theorem hessian_coercive (x : X) (y v : Y) :
    μ * ‖v‖ ^ 2 ≤ ⟪P.gyy x y v, v⟫ :=
  FrozenTilt.derivative_coercive (P.lower_strong_monotone x) y (P.gyy x y)
    (P.has_gyy x y) v

theorem hessian_inverse_norm (x : X) (y : Y) (J : Y →L[ℝ] Y)
    (hright : ∀ v, P.gyy x y (J v) = v) : ‖J‖ ≤ μ⁻¹ :=
  FrozenTilt.inverse_norm_bound (P.gyy x y) J P.μ_pos (P.hessian_coercive x y) hright

/-- In the finite-dimensional domain of the article, the Hessian inverse exists. -/
theorem hessian_inverse_exists [FiniteDimensional ℝ Y] (x : X) (y : Y) :
    ∃ J : Y →L[ℝ] Y, (∀ v, J (P.gyy x y v) = v) ∧
      (∀ v, P.gyy x y (J v) = v) ∧ ‖J‖ ≤ μ⁻¹ := by
  have hi : Function.Injective (P.gyy x y).toLinearMap := by
    intro u v huv
    have h := P.hessian_coercive x y (u - v)
    change P.gyy x y u = P.gyy x y v at huv
    rw [map_sub, huv, sub_self, inner_zero_left] at h
    have hn : ‖u - v‖ ^ 2 ≤ 0 := (mul_le_mul_left P.μ_pos).mp (by simpa using h)
    have hz : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  let e := LinearEquiv.ofBijective (P.gyy x y).toLinearMap
    ⟨hi, LinearMap.surjective_of_injective hi⟩
  let J := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hl : ∀ v, J (P.gyy x y v) = v := by
    intro v
    change e.symm (e v) = v
    exact e.symm_apply_apply v
  have hr : ∀ v, P.gyy x y (J v) = v := by
    intro v
    change e (e.symm v) = v
    exact e.apply_symm_apply v
  exact ⟨J, hl, hr, P.hessian_inverse_norm x y J hr⟩

theorem variation_yy_at_x (x : X) (u v : Y) :
    ‖P.gyy x u - P.gyy x v‖ ≤ ρ * ‖u - v‖ := by
  simpa [jointDistance] using P.variation_yy x x u v

theorem variation_xy_at_x (x : X) (u v : Y) :
    ‖P.gxy x u - P.gxy x v‖ ≤ ρ * ‖u - v‖ := by
  simpa [jointDistance] using P.variation_xy x x u v

/-- The frozen-tilt bias bound from the article's primitive model.

The output is compared to the explicit hypergradient formula. Its chain-rule
identification with the hyperobjective gradient remains a separate obligation.
-/
theorem frozen_tilt_bias (r : P.Response) (x : X) (yt : Y)
    (J : Y →L[ℝ] Y) {t : ℝ} (ht : 0 < t)
    (htilt : P.gy x yt = -t • P.fy x (r.y x))
    (hleft : ∀ v, J (P.gyy x (r.y x) v) = v)
    (hright : ∀ v, P.gyy x (r.y x) (J v) = v) :
    ‖FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x) yt t -
      FrozenTilt.hypergradient (P.fx x (r.y x)) (P.gxy x (r.y x)) J (P.fy x (r.y x))‖ ≤
        ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t := by
  exact FrozenTilt.ideal_estimator_bias (P.gy x) (P.gx x) (P.gyy x) (P.gxy x) J
    (r.y x) yt (P.fy x (r.y x)) (P.fx x (r.y x))
    ht P.μ_pos P.Lg_nonneg P.ρ_nonneg (P.lower_strong_monotone x)
    (P.minimizer_stationary x (r.y x) (r.minimizes x)) htilt (P.upper_bound x (r.y x))
    (P.has_gyy x) (P.has_gxy x) (P.variation_yy_at_x x) (P.variation_xy_at_x x)
    hleft (P.hessian_inverse_norm x (r.y x) J hright) (P.mixed_hessian_norm x (r.y x))

/-- Exactness at zero Hessian variation for every positive tilt size. -/
theorem frozen_tilt_exact_zero_variation (r : P.Response) (x : X) (yt : Y)
    (J : Y →L[ℝ] Y) {t : ℝ} (ht : 0 < t) (hvariation : ρ = 0)
    (htilt : P.gy x yt = -t • P.fy x (r.y x))
    (hleft : ∀ v, J (P.gyy x (r.y x) v) = v)
    (hright : ∀ v, P.gyy x (r.y x) (J v) = v) :
    FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x) yt t =
      FrozenTilt.hypergradient (P.fx x (r.y x)) (P.gxy x (r.y x)) J (P.fy x (r.y x)) := by
  have h := P.frozen_tilt_bias r x yt J ht htilt hleft hright
  have hc : ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t = 0 := by
    simp [hvariation]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (h.trans_eq hc))

end Bilevel.Model.Primitive
