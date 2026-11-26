import Bilevel.Model
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Existence of lower responses

Finite-dimensionality and the actual primitive strong-convexity inequality
imply coercivity and attainment. Linear tilts preserve the same inequality,
so their stationary responses also exist uniquely. No response-existence
certificate is assumed in these results.
-/

noncomputable section

namespace Bilevel.ResponseExistence

open Filter
open scoped Topology RealInnerProductSpace

/-- A positive quadratic lower bound dominates every fixed real threshold. -/
theorem coercive_of_quadratic_lower {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → ℝ) (μ c A : ℝ) (hμ : 0 < μ)
    (hbound : ∀ y, c - A * ‖y‖ + μ / 2 * ‖y‖ ^ 2 ≤ F y) :
    Tendsto F (cocompact E) atTop := by
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_norm_cocompact_atTop (E := E)).eventually_ge_atTop
    (max (2 * (A + 1) / μ) (b - c))
  filter_upwards [hn] with y hy
  have hrad : 2 * (A + 1) / μ ≤ ‖y‖ := le_trans (le_max_left _ _) hy
  have hb : b - c ≤ ‖y‖ := le_trans (le_max_right _ _) hy
  have hm := (div_le_iff₀ hμ).mp hrad
  have hmul := mul_le_mul_of_nonneg_right hm (norm_nonneg y)
  nlinarith [hbound y]

/-- A first-order strong-convexity lower model already supplies coercivity. -/
theorem coercive_of_strong_model {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → ℝ) (v : E) (μ : ℝ) (hμ : 0 < μ)
    (hmodel : ∀ y, F 0 + ⟪v, y⟫ + μ / 2 * ‖y‖ ^ 2 ≤ F y) :
    Tendsto F (cocompact E) atTop := by
  apply coercive_of_quadratic_lower F μ (F 0) ‖v‖ hμ
  intro y
  have hi := real_inner_le_norm (-v) y
  rw [inner_neg_left, norm_neg] at hi
  linarith [hmodel y]

end Bilevel.ResponseExistence

namespace Bilevel.Model.Primitive

open Filter
open scoped Topology RealInnerProductSpace

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem lower_continuous (x : X) : Continuous (P.g x) := by
  exact continuous_iff_continuousAt.mpr (fun y => (P.has_gy x y).hasFDerivAt.continuousAt)

theorem lower_coercive [FiniteDimensional ℝ Y] (x : X) :
    Tendsto (P.g x) (cocompact Y) atTop := by
  apply ResponseExistence.coercive_of_strong_model (P.g x) (P.gy x 0) μ P.μ_pos
  intro y
  simpa only [sub_zero] using P.strong_convex x 0 y

theorem lower_solution_exists [FiniteDimensional ℝ Y] (x : X) :
    ∃ y, P.IsLowerSolution x y := by
  exact (P.lower_continuous x).exists_forall_le (P.lower_coercive x)

theorem lower_solution_exists_unique [FiniteDimensional ℝ Y] (x : X) :
    ∃! y, P.IsLowerSolution x y := by
  obtain ⟨y, hy⟩ := P.lower_solution_exists x
  exact ⟨y, hy, fun v hv => P.lower_solution_unique x v y hv hy⟩

/-- A response is now constructed from Primitive in finite dimensions. -/
def canonicalResponse [FiniteDimensional ℝ Y] : P.Response where
  y x := Classical.choose (P.lower_solution_exists x)
  minimizes x := Classical.choose_spec (P.lower_solution_exists x)

theorem canonicalResponse_stationary [FiniteDimensional ℝ Y] (x : X) :
    P.gy x (P.canonicalResponse.y x) = 0 :=
  P.minimizer_stationary x _ (P.canonicalResponse.minimizes x)

/-- Primitive joint smoothness bounds the variation of the lower gradient in x. -/
theorem gy_lipschitz_x (x x' : X) (y : Y) :
    ‖P.gy x y - P.gy x' y‖ ≤ Lg * ‖x - x'‖ := by
  have h := P.smooth_g x x' y y
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  have hs : ‖P.gy x y - P.gy x' y‖ ^ 2 ≤ (Lg * ‖x - x'‖) ^ 2 := by
    nlinarith [sq_nonneg ‖P.gx x y - P.gx x' y‖]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg P.Lg_nonneg (norm_nonneg _))).mp hs

/-- The lower response is globally Lipschitz, derived from strong monotonicity. -/
theorem response_distance_bound (r : P.Response) (x x' : X) :
    ‖r.y x - r.y x'‖ ≤ (Lg / μ) * ‖x - x'‖ := by
  have hu := P.minimizer_stationary x (r.y x) (r.minimizes x)
  have hv := P.minimizer_stationary x' (r.y x') (r.minimizes x')
  have hs := (P.lower_strong_monotone x (r.y x) (r.y x')).trans
    (real_inner_le_norm (P.gy x (r.y x) - P.gy x (r.y x')) (r.y x - r.y x'))
  rw [hu, zero_sub, norm_neg] at hs
  have hn := P.gy_lipschitz_x x x' (r.y x')
  rw [hv, sub_zero] at hn
  have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg (r.y x - r.y x'))
  have hcomb : μ * ‖r.y x - r.y x'‖ ^ 2 ≤
      (Lg * ‖x - x'‖) * ‖r.y x - r.y x'‖ := hs.trans hm
  by_cases hz : ‖r.y x - r.y x'‖ = 0
  · rw [hz]
    exact mul_nonneg (div_nonneg P.Lg_nonneg P.μ_pos.le) (norm_nonneg _)
  · have hp : 0 < ‖r.y x - r.y x'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hc : μ * ‖r.y x - r.y x'‖ ≤ Lg * ‖x - x'‖ := by nlinarith
    have hd := (le_div_iff₀ P.μ_pos).mpr (show ‖r.y x - r.y x'‖ * μ ≤
      Lg * ‖x - x'‖ by nlinarith)
    simpa only [div_mul_eq_mul_div] using hd

theorem response_continuous (r : P.Response) : Continuous r.y := by
  have hk : 0 ≤ Lg / μ := div_nonneg P.Lg_nonneg P.μ_pos.le
  have hLip : LipschitzWith ⟨Lg / μ, hk⟩ r.y := by
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    simpa only [dist_eq_norm] using P.response_distance_bound r x x'
  exact hLip.continuous

/-- Fixed linear tilt of the lower objective. The scalar `t` need not be positive
for existence or preservation of the strong-convexity modulus. -/
def tiltedLower (x : X) (t : ℝ) (a y : Y) : ℝ := P.g x y + t * ⟪a, y⟫

theorem tilted_hasGradientAt (x : X) (t : ℝ) (a y : Y) :
    HasGradientAt (P.tiltedLower x t a) (P.gy x y + t • a) y := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hlin := ((InnerProductSpace.toDual ℝ Y) (t • a)).hasFDerivAt (x := y)
  have hadd := (P.has_gy x y).hasFDerivAt.add hlin
  simpa only [tiltedLower, map_add, InnerProductSpace.toDual_apply,
    real_inner_smul_left] using hadd

theorem tilted_strong_convex (x : X) (t : ℝ) (a u v : Y) :
    P.tiltedLower x t a u + ⟪P.gy x u + t • a, v - u⟫ +
      μ / 2 * ‖v - u‖ ^ 2 ≤ P.tiltedLower x t a v := by
  have h := P.strong_convex x u v
  simp only [tiltedLower, inner_add_left, real_inner_smul_left, inner_sub_right]
  simp only [inner_sub_right] at h
  nlinarith

theorem tilted_continuous (x : X) (t : ℝ) (a : Y) :
    Continuous (P.tiltedLower x t a) := by
  exact continuous_iff_continuousAt.mpr
    (fun y => (P.tilted_hasGradientAt x t a y).hasFDerivAt.continuousAt)

theorem tilted_coercive [FiniteDimensional ℝ Y] (x : X) (t : ℝ) (a : Y) :
    Tendsto (P.tiltedLower x t a) (cocompact Y) atTop := by
  apply ResponseExistence.coercive_of_strong_model (P.tiltedLower x t a)
    (P.gy x 0 + t • a) μ P.μ_pos
  intro y
  simpa only [sub_zero] using P.tilted_strong_convex x t a 0 y

theorem tilted_minimizer_exists [FiniteDimensional ℝ Y] (x : X) (t : ℝ) (a : Y) :
    ∃ y, ∀ v, P.tiltedLower x t a y ≤ P.tiltedLower x t a v :=
  (P.tilted_continuous x t a).exists_forall_le (P.tilted_coercive x t a)

theorem tilted_minimizer_stationary (x : X) (t : ℝ) (a y : Y)
    (h : ∀ v, P.tiltedLower x t a y ≤ P.tiltedLower x t a v) :
    P.gy x y = -t • a := by
  have hm : IsLocalMin (P.tiltedLower x t a) y := Filter.Eventually.of_forall h
  have hd := hm.hasFDerivAt_eq_zero (P.tilted_hasGradientAt x t a y).hasFDerivAt
  have hz : P.gy x y + t • a = 0 :=
    (InnerProductSpace.toDual ℝ Y).injective (by simpa using hd)
  have heq := eq_neg_of_add_eq_zero_left hz
  simpa only [neg_smul] using heq

theorem tilted_stationary_unique (x : X) (t : ℝ) (a u v : Y)
    (hu : P.gy x u = -t • a) (hv : P.gy x v = -t • a) : u = v := by
  have h := P.lower_strong_monotone x u v
  rw [hu, hv, sub_self, inner_zero_left] at h
  have hsq : ‖u - v‖ ^ 2 ≤ 0 := (mul_le_mul_left P.μ_pos).mp (by simpa using h)
  have hz : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem tilted_stationary_exists_unique [FiniteDimensional ℝ Y]
    (x : X) (t : ℝ) (a : Y) : ∃! y, P.gy x y = -t • a := by
  obtain ⟨y, hy⟩ := P.tilted_minimizer_exists x t a
  have hs := P.tilted_minimizer_stationary x t a y hy
  exact ⟨y, hs, fun v hv => P.tilted_stationary_unique x t a v y hv hs⟩

def tiltedResponse [FiniteDimensional ℝ Y] (x : X) (t : ℝ) (a : Y) : Y :=
  Classical.choose (P.tilted_minimizer_exists x t a)

theorem tiltedResponse_minimizes [FiniteDimensional ℝ Y] (x : X) (t : ℝ) (a : Y) :
    ∀ v, P.tiltedLower x t a (P.tiltedResponse x t a) ≤ P.tiltedLower x t a v :=
  Classical.choose_spec (P.tilted_minimizer_exists x t a)

theorem tiltedResponse_stationary [FiniteDimensional ℝ Y] (x : X) (t : ℝ) (a : Y) :
    P.gy x (P.tiltedResponse x t a) = -t • a :=
  P.tilted_minimizer_stationary x t a _ (P.tiltedResponse_minimizes x t a)

end Bilevel.Model.Primitive
