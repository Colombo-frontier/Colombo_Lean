import Bilevel.FrozenTilt
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Analytic model for the primitive assumptions

Gradients and Hessian blocks below come with derivative certificates. Strong
convexity is the first-order global inequality, not an uninterpreted predicate.
Joint bounds use the Euclidean sum-of-squares norm on the product. This file
does not yet define adaptive algorithms or prove existence of the response.
-/
noncomputable section
namespace Bilevel.Model
open scoped RealInnerProductSpace

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

def jointDistance (x x' : X) (y y' : Y) : ℝ :=
  Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)

/-- Source Assumption `ass:primitive`, excluding the separate gap certificate. -/
structure Primitive (μ Lf Lg Cf ρ : ℝ) where
  μ_pos : 0 < μ
  Lf_nonneg : 0 ≤ Lf
  Lg_nonneg : 0 ≤ Lg
  Cf_nonneg : 0 ≤ Cf
  ρ_nonneg : 0 ≤ ρ
  f : X → Y → ℝ
  g : X → Y → ℝ
  fx : X → Y → X
  fy : X → Y → Y
  gx : X → Y → X
  gy : X → Y → Y
  gyy : X → Y → (Y →L[ℝ] Y)
  gxy : X → Y → (Y →L[ℝ] X)
  has_fx : ∀ x y, HasGradientAt (fun x => f x y) (fx x y) x
  has_fy : ∀ x y, HasGradientAt (f x) (fy x y) y
  has_gx : ∀ x y, HasGradientAt (fun x => g x y) (gx x y) x
  has_gy : ∀ x y, HasGradientAt (g x) (gy x y) y
  has_gyy : ∀ x y, HasFDerivAt (gy x) (gyy x y) y
  has_gxy : ∀ x y, HasFDerivAt (gx x) (gxy x y) y
  strong_convex : ∀ x u v,
    g x u + ⟪gy x u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ g x v
  upper_bound : ∀ x y, ‖fy x y‖ ≤ Cf
  smooth_f : ∀ x x' y y',
    ‖fx x y - fx x' y'‖ ^ 2 + ‖fy x y - fy x' y'‖ ^ 2 ≤
      Lf ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  smooth_g : ∀ x x' y y',
    ‖gx x y - gx x' y'‖ ^ 2 + ‖gy x y - gy x' y'‖ ^ 2 ≤
      Lg ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  variation_yy : ∀ x x' y y',
    ‖gyy x y - gyy x' y'‖ ≤ ρ * jointDistance x x' y y'
  variation_xy : ∀ x x' y y',
    ‖gxy x y - gxy x' y'‖ ≤ ρ * jointDistance x x' y y'

namespace Primitive
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

def IsLowerSolution (x : X) (y : Y) : Prop := ∀ v, P.g x y ≤ P.g x v

theorem lower_strong_monotone (x : X) : FrozenTilt.StrongMonotone (P.gy x) μ := by
  intro u v
  have h1 := P.strong_convex x u v
  have h2 := P.strong_convex x v u
  rw [norm_sub_rev v u] at h1
  have hi : ⟪P.gy x u, v - u⟫ + ⟪P.gy x v, u - v⟫ =
      -⟪P.gy x u - P.gy x v, u - v⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right]
    ring
  nlinarith

theorem stationary_minimizes (x : X) (y : Y) (h : P.gy x y = 0) :
    P.IsLowerSolution x y := by
  intro v
  have hs := P.strong_convex x y v
  rw [h, inner_zero_left, add_zero] at hs
  have hn : 0 ≤ μ / 2 * ‖v - y‖ ^ 2 :=
    mul_nonneg (div_nonneg P.μ_pos.le (by norm_num)) (sq_nonneg _)
  linarith

theorem minimizer_stationary (x : X) (y : Y) (h : P.IsLowerSolution x y) :
    P.gy x y = 0 := by
  have hm : IsLocalMin (P.g x) y := Filter.Eventually.of_forall h
  have hd := hm.hasFDerivAt_eq_zero (P.has_gy x y).hasFDerivAt
  exact (InnerProductSpace.toDual ℝ Y).injective (by simpa using hd)

theorem stationary_unique (x : X) (u v : Y) (hu : P.gy x u = 0) (hv : P.gy x v = 0) :
    u = v := by
  have h := P.lower_strong_monotone x u v
  rw [hu, hv, sub_self, inner_zero_left] at h
  have hsq : ‖u - v‖ ^ 2 ≤ 0 := (mul_le_mul_left P.μ_pos).mp (by simpa using h)
  have hz : ‖u - v‖ = 0 := by nlinarith [sq_nonneg ‖u - v‖, norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem lower_solution_unique (x : X) (u v : Y)
    (hu : P.IsLowerSolution x u) (hv : P.IsLowerSolution x v) : u = v :=
  P.stationary_unique x u v (P.minimizer_stationary x u hu) (P.minimizer_stationary x v hv)

/-- A response is supplied with its minimization proof; existence is not assumed in Primitive. -/
structure Response where
  y : X → Y
  minimizes : ∀ x, P.IsLowerSolution x (y x)

def hyperobjective (r : P.Response) (x : X) : ℝ := P.f x (r.y x)

/-- Lower bound witness avoids undefined real infima for unbounded objectives. -/
structure GapCertificate (r : P.Response) (x₀ : X) (Δ : ℝ) where
  floor : ℝ
  lower_bound : ∀ x, floor ≤ P.hyperobjective r x
  gap : P.hyperobjective r x₀ - floor ≤ Δ

end Primitive
end Bilevel.Model
