import Bilevel.HypergradientFormula

/-! Pathwise error of an implementable frozen-tilt estimator. -/
noncomputable section
namespace Bilevel.Model.Primitive
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

omit [FiniteDimensional ℝ Y] in
theorem fx_lipschitz_y (x : X) (u v : Y) : ‖P.fx x u - P.fx x v‖ ≤ Lf * ‖u - v‖ := by
  apply JointDerivative.component_bound P.Lf_nonneg (norm_nonneg (u - v)) (v := P.fy x u - P.fy x v)
  simpa using P.smooth_f x x u v

omit [FiniteDimensional ℝ Y] in
theorem fy_lipschitz_y (x : X) (u v : Y) : ‖P.fy x u - P.fy x v‖ ≤ Lf * ‖u - v‖ := by
  apply JointDerivative.component_bound P.Lf_nonneg (norm_nonneg (u - v)) (v := P.fx x u - P.fx x v)
  have h := P.smooth_f x x u v
  simpa [add_comm] using h

theorem tilt_direction_stability (r : P.Response) (x : X) (a b : Y) {t : ℝ} (ht : 0 < t) :
    ‖FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x) (P.tiltedResponse x t a) t -
      FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x) (P.tiltedResponse x t b) t‖ ≤
      Lg / μ * ‖a - b‖ :=
  FrozenTilt.estimator_stability _ P.μ_pos ht P.Lg_nonneg (P.lower_strong_monotone x)
    (P.tiltedResponse_stationary x t a) (P.tiltedResponse_stationary x t b) (P.gx_lipschitz_y x)

def sampledEstimator (x : X) (y₀ yₜ : Y) (ef eg₀ egₜ : X) (t : ℝ) : X :=
  P.fx x y₀ + ef + t⁻¹ • ((P.gx x yₜ + egₜ) - (P.gx x y₀ + eg₀))

theorem estimator_solver_noise_bound (r : P.Response) (x : X) (y₀ yₜ a : Y)
    (ef eg₀ egₜ : X) {t : ℝ} (ht : 0 < t) :
    ‖P.sampledEstimator x y₀ yₜ ef eg₀ egₜ t -
      FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x) (P.tiltedResponse x t a) t‖ ≤
      Lf * ‖y₀ - r.y x‖ + ‖ef‖ + t⁻¹ *
        (Lg * ‖yₜ - P.tiltedResponse x t a‖ + Lg * ‖y₀ - r.y x‖ + ‖egₜ‖ + ‖eg₀‖) := by
  let dx := P.fx x y₀ - P.fx x (r.y x)
  let dg := (P.gx x yₜ - P.gx x (P.tiltedResponse x t a)) - (P.gx x y₀ - P.gx x (r.y x))
  have he : P.sampledEstimator x y₀ yₜ ef eg₀ egₜ t -
      FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x) (P.tiltedResponse x t a) t =
      dx + ef + t⁻¹ • (dg + egₜ - eg₀) := by
    dsimp [sampledEstimator, FrozenTilt.estimator, dx, dg]
    module
  rw [he]
  have hdx : ‖dx‖ ≤ Lf * ‖y₀ - r.y x‖ := P.fx_lipschitz_y x y₀ (r.y x)
  have hdg : ‖dg‖ ≤ Lg * ‖yₜ - P.tiltedResponse x t a‖ + Lg * ‖y₀ - r.y x‖ := by
    exact (norm_sub_le _ _).trans (add_le_add (P.gx_lipschitz_y x _ _) (P.gx_lipschitz_y x _ _))
  calc
    ‖dx + ef + t⁻¹ • (dg + egₜ - eg₀)‖ ≤ ‖dx‖ + ‖ef‖ + ‖t⁻¹ • (dg + egₜ - eg₀)‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ = ‖dx‖ + ‖ef‖ + t⁻¹ * ‖dg + egₜ - eg₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    _ ≤ _ := by
      have hsum : ‖dg + egₜ - eg₀‖ ≤ ‖dg‖ + ‖egₜ‖ + ‖eg₀‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      gcongr
      exact hsum.trans (by linarith)

/-- Complete deterministic perturbation bound: solver errors, frozen-direction
error, fresh gradient errors, and analytic bias are all exposed. -/
theorem sampledEstimator_gradient_error (r : P.Response) (x : X) (y₀ yₜ a : Y)
    (ef eg₀ egₜ : X) {t : ℝ} (ht : 0 < t) :
    ‖P.sampledEstimator x y₀ yₜ ef eg₀ egₜ t - gradient (P.hyperobjective r) x‖ ≤
      Lf * ‖y₀ - r.y x‖ + ‖ef‖ + t⁻¹ *
        (Lg * ‖yₜ - P.tiltedResponse x t a‖ + Lg * ‖y₀ - r.y x‖ + ‖egₜ‖ + ‖eg₀‖) +
      Lg / μ * ‖a - P.fy x (r.y x)‖ + ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t := by
  let ha := FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x) (P.tiltedResponse x t a) t
  let h0 := FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x)
    (P.tiltedResponse x t (P.fy x (r.y x))) t
  have htri := dist_triangle (P.sampledEstimator x y₀ yₜ ef eg₀ egₜ t) ha (gradient (P.hyperobjective r) x)
  have htri2 := dist_triangle ha h0 (gradient (P.hyperobjective r) x)
  simp only [dist_eq_norm] at htri htri2
  have h1 := P.estimator_solver_noise_bound r x y₀ yₜ a ef eg₀ egₜ ht
  have h2 := P.tilt_direction_stability r x a (P.fy x (r.y x)) ht
  have h3 := P.frozen_tilt_gradient_bias r x ht
  dsimp [ha, h0] at htri htri2
  linarith

end Bilevel.Model.Primitive
