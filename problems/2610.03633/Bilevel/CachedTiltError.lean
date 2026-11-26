import Bilevel.EstimatorPerturbation
import Bilevel.Curvature
import Bilevel.Clipping

/-! Pointwise cached-gradient error, `cache:lem:error` in the chi refinement.
The anchor and both current lower solves may be arbitrary. Only their realized
accuracy certificates are used; no unbiasedness of a reused sample is assumed.
The gradient in the conclusion is the derivative of the actual hyperobjective.
-/
noncomputable section
namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

def cachedEstimator (x : X) (y₀ yₜ : Y) (b eg₀ egₜ : X) (t : ℝ) : X :=
  b + t⁻¹ • ((P.gx x yₜ + egₜ) - (P.gx x y₀ + eg₀))

theorem cached_solver_error (r : P.Response) (x : X) (y₀ yₜ a : Y)
    (b eg₀ egₜ : X) {t : ℝ} (ht : 0 < t) :
    ‖P.cachedEstimator x y₀ yₜ b eg₀ egₜ t -
      FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x)
        (P.tiltedResponse x t a) t‖ ≤
      ‖b - P.fx x (r.y x)‖ + t⁻¹ *
        (Lg * ‖yₜ - P.tiltedResponse x t a‖ + Lg * ‖y₀ - r.y x‖ +
          ‖egₜ‖ + ‖eg₀‖) := by
  let dg := (P.gx x yₜ - P.gx x (P.tiltedResponse x t a)) -
    (P.gx x y₀ - P.gx x (r.y x))
  have he : P.cachedEstimator x y₀ yₜ b eg₀ egₜ t -
      FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x)
        (P.tiltedResponse x t a) t =
      (b - P.fx x (r.y x)) + t⁻¹ • (dg + egₜ - eg₀) := by
    dsimp [cachedEstimator, FrozenTilt.estimator, dg]
    module
  have hdg : ‖dg‖ ≤ Lg * ‖yₜ - P.tiltedResponse x t a‖ +
      Lg * ‖y₀ - r.y x‖ :=
    (norm_sub_le _ _).trans (add_le_add (P.gx_lipschitz_y x _ _)
      (P.gx_lipschitz_y x _ _))
  rw [he]
  calc
    _ ≤ ‖b - P.fx x (r.y x)‖ + ‖t⁻¹ • (dg + egₜ - eg₀)‖ := norm_add_le _ _
    _ = ‖b - P.fx x (r.y x)‖ + t⁻¹ * ‖dg + egₜ - eg₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    _ ≤ _ := by
      have hs : ‖dg + egₜ - eg₀‖ ≤ ‖dg‖ + ‖egₜ‖ + ‖eg₀‖ :=
        (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      gcongr
      linarith

theorem cached_gradient_error (r : P.Response) (x : X) (y₀ yₜ a : Y)
    (b eg₀ egₜ : X) {t : ℝ} (ht : 0 < t) :
    ‖P.cachedEstimator x y₀ yₜ b eg₀ egₜ t - gradient (P.hyperobjective r) x‖ ≤
      ‖b - P.fx x (r.y x)‖ + Lg / μ * ‖a - P.fy x (r.y x)‖ +
      t⁻¹ * (Lg * ‖yₜ - P.tiltedResponse x t a‖ + Lg * ‖y₀ - r.y x‖ +
        ‖egₜ‖ + ‖eg₀‖) + ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t := by
  let ha := FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x)
    (P.tiltedResponse x t a) t
  let h0 := FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x)
    (P.tiltedResponse x t (P.fy x (r.y x))) t
  have h1 := P.cached_solver_error r x y₀ yₜ a b eg₀ egₜ ht
  have h2 := P.tilt_direction_stability r x a (P.fy x (r.y x)) ht
  have h3 := P.frozen_tilt_gradient_bias r x ht
  have h4 := dist_triangle (P.cachedEstimator x y₀ yₜ b eg₀ egₜ t) ha
    (gradient (P.hyperobjective r) x)
  have h5 := dist_triangle ha h0 (gradient (P.hyperobjective r) x)
  simp only [dist_eq_norm] at h4 h5
  dsimp [ha, h0] at h4 h5
  linarith

omit [FiniteDimensional ℝ Y] in
/-- Both cached components are compared to the current response graph. -/
theorem cached_anchor_error (r : P.Response) (x anchor : X) (ya raw : Y) (b : X)
    {η : ℝ} (hb : ‖b - P.fx anchor ya‖ ≤ η) (ha : ‖raw - P.fy anchor ya‖ ≤ η) :
    ‖b - P.fx x (r.y x)‖ + Lg / μ *
      ‖Clipping.clip Cf raw - P.fy x (r.y x)‖ ≤
      (1 + Lg / μ) * (η + Lf * ‖ya - r.y anchor‖ +
        Lf * (1 + Lg / μ) * ‖anchor - x‖) := by
  have hk : 0 ≤ Lg / μ := div_nonneg P.Lg_nonneg P.μ_pos.le
  have hgraph := P.response_joint_distance r anchor x
  have hc := P.upper_component_bounds anchor x (r.y anchor) (r.y x)
  have hbx : ‖b - P.fx x (r.y x)‖ ≤
      η + Lf * ‖ya - r.y anchor‖ + Lf * (1 + Lg / μ) * ‖anchor - x‖ := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub b (P.fx anchor ya) (P.fx x (r.y x))
    have h2 := norm_sub_le_norm_sub_add_norm_sub (P.fx anchor ya)
      (P.fx anchor (r.y anchor)) (P.fx x (r.y x))
    have h3 := P.fx_lipschitz_y anchor ya (r.y anchor)
    have h4 := hc.1.trans (mul_le_mul_of_nonneg_left hgraph P.Lf_nonneg)
    nlinarith
  have hay : ‖Clipping.clip Cf raw - P.fy x (r.y x)‖ ≤
      η + Lf * ‖ya - r.y anchor‖ + Lf * (1 + Lg / μ) * ‖anchor - x‖ := by
    have hp := Clipping.error_nonincreasing Cf P.Cf_nonneg raw
      (P.fy x (r.y x)) (P.upper_bound x (r.y x))
    have h1 := norm_sub_le_norm_sub_add_norm_sub raw (P.fy anchor ya) (P.fy x (r.y x))
    have h2 := norm_sub_le_norm_sub_add_norm_sub (P.fy anchor ya)
      (P.fy anchor (r.y anchor)) (P.fy x (r.y x))
    have h3 := P.fy_lipschitz_y anchor ya (r.y anchor)
    have h4 := hc.2.trans (mul_le_mul_of_nonneg_left hgraph P.Lf_nonneg)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hay hk
  nlinarith

/-- The manuscript's simultaneous accuracy certificates, with C = 64.
The multiplied inequalities also cover zero upper smoothness without division
by zero; positive-parameter radius choices in the text imply these budgets. -/
theorem cached_pointwise_accuracy (r : P.Response) (x anchor : X)
    (ya y₀ yₜ raw : Y) (b eg₀ egₜ : X) {t ε η : ℝ} (ht : 0 < t)
    (hb : ‖b - P.fx anchor ya‖ ≤ η) (ha : ‖raw - P.fy anchor ya‖ ≤ η)
    (hη : (1 + Lg / μ) * η ≤ ε / 64)
    (hA : (1 + Lg / μ) * Lf * ‖ya - r.y anchor‖ ≤ ε / 64)
    (hx : Lf * (1 + Lg / μ)^2 * ‖anchor - x‖ ≤ ε / 64)
    (h₀ : Lg * ‖y₀ - r.y x‖ ≤ ε * t / 64)
    (hₜ : Lg * ‖yₜ - P.tiltedResponse x t (Clipping.clip Cf raw)‖ ≤ ε * t / 64)
    (hg₀ : ‖eg₀‖ ≤ ε * t / 64) (hgₜ : ‖egₜ‖ ≤ ε * t / 64)
    (hbias : ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t ≤ ε / 64) :
    ‖P.cachedEstimator x y₀ yₜ b eg₀ egₜ t - gradient (P.hyperobjective r) x‖ ≤ ε / 8 := by
  have han := P.cached_anchor_error r x anchor ya raw b hb ha
  have he := P.cached_gradient_error r x y₀ yₜ (Clipping.clip Cf raw) b eg₀ egₜ ht
  have hsum : Lg * ‖yₜ - P.tiltedResponse x t (Clipping.clip Cf raw)‖ +
      Lg * ‖y₀ - r.y x‖ + ‖egₜ‖ + ‖eg₀‖ ≤ ε * t / 16 := by linarith
  have hm := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr ht.le)
  have hc : t⁻¹ * (ε * t / 16) = ε / 16 := by field_simp
  rw [hc] at hm
  nlinarith

end Bilevel.Model.Primitive
