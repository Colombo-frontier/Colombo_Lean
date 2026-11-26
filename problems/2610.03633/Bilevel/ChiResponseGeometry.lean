import Bilevel.SourcePrimitive
import Bilevel.EstimatorPerturbation
import Bilevel.Curvature

/-! Source-facing response/tilt geometry for `up:lem:estimator-geometry`.
All responses below are constructed by minimum attainment. The assumptions
are full Euclidean gradient budgets, not a postulated hypergradient formula.
-/
noncomputable section
namespace Bilevel.ChiResponseGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {μ Lf Lg Cf ρ : ℝ}
  (P : PrimitiveGeometry.FullPrimitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

def response (x : X) : Y := P.toPrimitive.canonicalResponse.y x

def hyperobjective (x : X) : ℝ := P.f (PrimitiveGeometry.pack x (response P x))

def tilt (x : X) (t : ℝ) (a : Y) : Y := P.toPrimitive.tiltedResponse x t a

def estimator (x : X) (t : ℝ) (a : Y) : X :=
  FrozenTilt.estimator (P.toPrimitive.fx x (response P x)) (P.toPrimitive.gx x)
    (response P x) (tilt P x t a) t

theorem response_minimizes (x : X) : ∀ y,
    P.g (PrimitiveGeometry.pack x (response P x)) ≤ P.g (PrimitiveGeometry.pack x y) :=
  P.toPrimitive.canonicalResponse.minimizes x

theorem response_unique (x : X) (y : Y)
    (hy : ∀ z, P.g (PrimitiveGeometry.pack x y) ≤ P.g (PrimitiveGeometry.pack x z)) :
    y = response P x :=
  P.toPrimitive.lower_solution_unique x y (response P x) hy (response_minimizes P x)

theorem response_lipschitz (x z : X) :
    ‖response P x - response P z‖ ≤ Lg / μ * ‖x-z‖ :=
  P.toPrimitive.response_distance_bound P.toPrimitive.canonicalResponse x z

theorem tilt_minimizes (x : X) (t : ℝ) (a : Y) : ∀ y,
    P.toPrimitive.tiltedLower x t a (tilt P x t a) ≤ P.toPrimitive.tiltedLower x t a y :=
  P.toPrimitive.tiltedResponse_minimizes x t a

theorem tilt_displacement (x : X) {t : ℝ} (ht : 0 < t) (a : Y) (ha : ‖a‖ ≤ Cf) :
    ‖tilt P x t a - response P x‖ ≤ t * Cf / μ :=
  FrozenTilt.solution_displacement P.μ_pos ht (P.toPrimitive.lower_strong_monotone x)
    (P.toPrimitive.canonicalResponse_stationary x)
    (P.toPrimitive.tiltedResponse_stationary x t a) ha

theorem tilt_stability (x : X) {t : ℝ} (ht : 0 < t) (a b : Y) :
    ‖tilt P x t a - tilt P x t b‖ ≤ t / μ * ‖a-b‖ :=
  FrozenTilt.solution_stability P.μ_pos ht (P.toPrimitive.lower_strong_monotone x)
    (P.toPrimitive.tiltedResponse_stationary x t a)
    (P.toPrimitive.tiltedResponse_stationary x t b)

theorem estimator_stability (x : X) {t : ℝ} (ht : 0 < t) (a b : Y) :
    ‖estimator P x t a - estimator P x t b‖ ≤ Lg / μ * ‖a-b‖ :=
  P.toPrimitive.tilt_direction_stability P.toPrimitive.canonicalResponse x a b ht

theorem estimator_bias (x : X) {t : ℝ} (ht : 0 < t) :
    ‖estimator P x t (P.toPrimitive.fy x (response P x)) - gradient (hyperobjective P) x‖ ≤
      ((1 + Lg / μ) * ρ * Cf^2 / (2 * μ^2)) * t :=
  P.toPrimitive.frozen_tilt_gradient_bias P.toPrimitive.canonicalResponse x ht

theorem zero_variation_exact (hρ : ρ = 0) (x : X) {t : ℝ} (ht : 0 < t) :
    estimator P x t (P.toPrimitive.fy x (response P x)) = gradient (hyperobjective P) x := by
  have h := estimator_bias P x ht
  simp only [hρ, mul_zero, zero_mul, zero_div] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem hyperobjective_curvature (x z : X) :
    ‖gradient (hyperobjective P) x - gradient (hyperobjective P) z‖ ≤
      ((1 + Lg / μ)^2 * (Lf + ρ * Cf / μ)) * ‖x-z‖ :=
  P.toPrimitive.gradient_hyperobjective_norm_sub_le P.toPrimitive.canonicalResponse x z

/-- The public initialization radius remains valid at every capped point,
including points reached after previous oracle failures. -/
theorem uniform_tilt_initialization (x x₀ : X) (yinit a : Y) {t R₀ R : ℝ}
    (ht : 0 < t) (ha : ‖a‖ ≤ Cf)
    (hinit : ‖yinit - response P x₀‖ ≤ R₀) (hx : ‖x-x₀‖ ≤ R) :
    ‖yinit - tilt P x t a‖ ≤ R₀ + Lg / μ * R + t * Cf / μ := by
  have h1 := norm_sub_le_norm_sub_add_norm_sub yinit (response P x₀) (tilt P x t a)
  have h2 := norm_sub_le_norm_sub_add_norm_sub (response P x₀) (response P x) (tilt P x t a)
  have hr := response_lipschitz P x x₀
  have hd := tilt_displacement P x ht a ha
  rw [norm_sub_rev (response P x₀) (response P x)] at h2
  rw [norm_sub_rev (response P x) (tilt P x t a)] at h2
  have hmove := hr.trans (mul_le_mul_of_nonneg_left hx (div_nonneg P.Lg_nonneg P.μ_pos.le))
  linarith

end Bilevel.ChiResponseGeometry
