import Bilevel.SourcePrimitive
import Bilevel.Curvature
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Source-facing population assumptions. Joint norms use the Euclidean L2
product. The lower response and hypergradient are derived, not certificate fields.
The first-order strong-convexity inequality is the differentiable convention. -/
noncomputable section
open scoped RealInnerProductSpace
open Bilevel.PrimitiveGeometry
namespace Smoothness2601

structure Budgets where
  μ : ℝ
  L₀ : ℝ
  L₁ : ℝ
  L₂ : ℝ
  Δ : ℝ
  σ : ℝ
  R₀ : ℝ
  μ_pos : 0 < μ
  L₀_pos : 0 < L₀
  L₁_pos : 0 < L₁
  L₂_pos : 0 < L₂
  Δ_pos : 0 < Δ
  σ_pos : 0 < σ
  R₀_nonneg : 0 ≤ R₀

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Assumption `ass:population`, before initialization and the objective gap. -/
structure Population (b : Budgets) where
  f : Joint X Y → ℝ
  g : Joint X Y → ℝ
  grad_f : Joint X Y → Joint X Y
  grad_g : Joint X Y → Joint X Y
  has_f : ∀ z, HasGradientAt f (grad_f z) z
  has_g : ∀ z, HasGradientAt g (grad_g z) z
  gyy : X → Y → (Y →L[ℝ] Y)
  gxy : X → Y → (Y →L[ℝ] X)
  has_gyy : ∀ x y, HasFDerivAt (fun v => (grad_g (pack x v)).snd) (gyy x y) y
  has_gxy : ∀ x y, HasFDerivAt (fun v => (grad_g (pack x v)).fst) (gxy x y) y
  strong_convex : ∀ x u v, g (pack x u) + ⟪(grad_g (pack x u)).snd, v-u⟫ +
    b.μ / 2 * ‖v-u‖^2 ≤ g (pack x v)
  lipschitz_f_y : ∀ x u v, ‖f (pack x u) - f (pack x v)‖ ≤ b.L₀ * ‖u-v‖
  smooth_f : ∀ z w, ‖grad_f z - grad_f w‖ ≤ b.L₁ * ‖z-w‖
  smooth_g : ∀ z w, ‖grad_g z - grad_g w‖ ≤ b.L₁ * ‖z-w‖
  variation_yy : ∀ x x' y y', ‖gyy x y - gyy x' y'‖ ≤ b.L₂ * ‖pack x y-pack x' y'‖
  variation_xy : ∀ x x' y y', ‖gxy x y - gxy x' y'‖ ≤ b.L₂ * ‖pack x y-pack x' y'‖

namespace Population
variable {b : Budgets} (P : Population (X := X) (Y := Y) b)

theorem lower_upper_gradient_bound (x : X) (y : Y) :
    ‖(P.grad_f (pack x y)).snd‖ ≤ b.L₀ := by
  have h := (partial_y (P.has_f (pack x y))).hasFDerivAt.le_of_lip' b.L₀_pos.le
    (Filter.Eventually.of_forall (fun v => P.lipschitz_f_y x v y))
  simpa using h

def toFullPrimitive : FullPrimitive (X := X) (Y := Y) b.μ b.L₁ b.L₁ b.L₀ b.L₂ where
  μ_pos := b.μ_pos
  Lf_nonneg := b.L₁_pos.le
  Lg_nonneg := b.L₁_pos.le
  Cf_nonneg := b.L₀_pos.le
  ρ_nonneg := b.L₂_pos.le
  f := P.f
  g := P.g
  grad_f := P.grad_f
  grad_g := P.grad_g
  has_f := P.has_f
  has_g := P.has_g
  gyy := P.gyy
  gxy := P.gxy
  has_gyy := P.has_gyy
  has_gxy := P.has_gxy
  strong_convex := P.strong_convex
  upper_bound z := P.lower_upper_gradient_bound z.fst z.snd
  smooth_f := P.smooth_f
  smooth_g := P.smooth_g
  variation_yy := P.variation_yy
  variation_xy := P.variation_xy

def primitive := P.toFullPrimitive.toPrimitive

/-- The exact finite derivative list, with no derivative beyond its top Lipschitz
order required. `L 2` is the separately fixed baseline budget. -/
def HigherRegularity (p : WithTop ℕ) (L : ℕ → ℝ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → (q + 1 : ℕ) ≤ p → ∀ x : X,
    ContDiff ℝ q (fun y => P.grad_f (pack x y)) ∧
    ContDiff ℝ (q+1) (fun y => P.grad_g (pack x y)) ∧
    (∀ u v : Y,
      ‖iteratedFDeriv ℝ q (fun y => P.grad_f (pack x y)) u -
        iteratedFDeriv ℝ q (fun y => P.grad_f (pack x y)) v‖ ≤ L (q+1) * ‖u-v‖) ∧
    (∀ u v : Y,
      ‖iteratedFDeriv ℝ (q+1) (fun y => P.grad_g (pack x y)) u -
        iteratedFDeriv ℝ (q+1) (fun y => P.grad_g (pack x y)) v‖ ≤ L (q+2) * ‖u-v‖)

theorem higherRegularity_mono_budgets {p : WithTop ℕ} {L K : ℕ → ℝ}
    (hL : ∀ j, L j ≤ K j) (h : P.HigherRegularity p L) : P.HigherRegularity p K := by
  intro q hq hp x
  obtain ⟨hf,hg,hfb,hgb⟩ := h q hq hp x
  refine ⟨hf,hg,?_,?_⟩
  · intro u v
    exact (hfb u v).trans (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))
  · intro u v
    exact (hgb u v).trans (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))

theorem higherRegularity_mono_order {p r : WithTop ℕ} {L : ℕ → ℝ}
    (hrp : r ≤ p) (h : P.HigherRegularity p L) : P.HigherRegularity r L := by
  intro q hq hqr x
  exact h q hq (hqr.trans hrp) x

theorem higherRegularity_one (L : ℕ → ℝ) : P.HigherRegularity 1 L := by
  intro q hq hp
  have hp' : q + 1 ≤ 1 := by exact_mod_cast hp
  omega

variable [FiniteDimensional ℝ Y]

def yStar (x : X) : Y := P.primitive.canonicalResponse.y x
def objective (x : X) : ℝ := P.f (pack x (P.yStar x))

theorem yStar_minimizes (x : X) (y : Y) :
    P.g (pack x (P.yStar x)) ≤ P.g (pack x y) :=
  P.primitive.canonicalResponse.minimizes x y

theorem yStar_unique (x : X) (y : Y)
    (hy : ∀ v, P.g (pack x y) ≤ P.g (pack x v)) : y = P.yStar x :=
  P.primitive.lower_solution_unique x y (P.yStar x) hy
    (P.primitive.canonicalResponse.minimizes x)

/-- Equation `eq:main-hyper` for the actual composed objective. -/
theorem actual_hypergradient (x : X) :
    gradient P.objective x = (P.grad_f (pack x (P.yStar x))).fst -
      P.gxy x (P.yStar x)
        (P.primitive.inverseAt x (P.yStar x) (P.grad_f (pack x (P.yStar x))).snd) :=
  P.primitive.gradient_hyperobjective P.primitive.canonicalResponse x

theorem hypergradient_lipschitz (x z : X) :
    ‖gradient P.objective x - gradient P.objective z‖ ≤
      ((1+b.L₁/b.μ)^2*(b.L₁+b.L₂*b.L₀/b.μ)) * ‖x-z‖ :=
  P.primitive.gradient_hyperobjective_norm_sub_le P.primitive.canonicalResponse x z

/-- Starting-point and finite-gap clauses, stated using the actual minimizer. -/
structure Initialized (x₀ : X) (y₀ : Y) : Prop where
  bounded_below : BddBelow (Set.range P.objective)
  initial_gap : P.objective x₀ - sInf (Set.range P.objective) ≤ b.Δ
  inner_error : ‖y₀ - P.yStar x₀‖ ≤ b.R₀

end Population
end Smoothness2601
