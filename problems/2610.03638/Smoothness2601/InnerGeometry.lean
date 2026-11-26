import Smoothness2601.Population

/-! The manuscript's ordinary-inner SGD contraction is derived from the
actual population gradient, strong monotonicity and smoothness. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Smoothness2601.InnerGeometry

def stepsize (b : Budgets) : ℝ := b.μ / b.L₁ ^ 2
def rate (b : Budgets) : ℝ := 1 - b.μ ^ 2 / b.L₁ ^ 2

theorem stepsize_pos (b : Budgets) : 0 < stepsize b :=
  div_pos b.μ_pos (sq_pos_of_pos b.L₁_pos)

theorem rate_range (b : Budgets) (hgap : b.μ < b.L₁) : 0 < rate b ∧ rate b < 1 := by
  have hratio : b.μ ^ 2 / b.L₁ ^ 2 < 1 := by
    apply (div_lt_one (sq_pos_of_pos b.L₁_pos)).mpr
    nlinarith [b.μ_pos, b.L₁_pos]
  have hp : 0 < b.μ ^ 2 / b.L₁ ^ 2 := div_pos (sq_pos_of_pos b.μ_pos) (sq_pos_of_pos b.L₁_pos)
  constructor <;> dsimp [rate] <;> linarith

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {b : Budgets}
  (P : Population (X := X) (Y := Y) b)

theorem lower_stationary (x : X) : P.primitive.gy x (P.yStar x) = 0 :=
  P.primitive.minimizer_stationary x _ (P.primitive.canonicalResponse.minimizes x)

theorem contraction (x : X) (y : Y) :
    ‖y - stepsize b • P.primitive.gy x y - P.yStar x‖ ^ 2 ≤
      rate b * ‖y - P.yStar x‖ ^ 2 := by
  have hstat := lower_stationary P x
  have hs := P.primitive.lower_strong_monotone x y (P.yStar x)
  have hl := P.primitive.gy_lipschitz_y x y (P.yStar x)
  rw [hstat, sub_zero] at hs hl
  have hα := (stepsize_pos b).le
  have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hα)
  have hl' := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg b.L₁_pos.le (norm_nonneg _))).mpr hl
  have hl'' := mul_le_mul_of_nonneg_left hl' (sq_nonneg (stepsize b))
  have he : y - stepsize b • P.primitive.gy x y - P.yStar x =
      (y - P.yStar x) - stepsize b • P.primitive.gy x y := by abel
  rw [he, norm_sub_sq_real, real_inner_smul_right, real_inner_comm,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  have hc : 1 - 2 * stepsize b * b.μ + stepsize b ^ 2 * b.L₁ ^ 2 = rate b := by
    dsimp [stepsize, rate]
    field_simp [ne_of_gt b.L₁_pos]
    ring
  calc
    _ ≤ (1 - 2 * stepsize b * b.μ + stepsize b ^ 2 * b.L₁ ^ 2) *
        ‖y-P.yStar x‖ ^ 2 := by nlinarith
    _ = _ := by rw [hc]

theorem initial_radius (x₀ x : X) (y₀ : Y) {R : ℝ}
    (hinit : ‖y₀-P.yStar x₀‖ ≤ b.R₀) (hdistance : ‖x-x₀‖ ≤ R) :
    ‖y₀-P.yStar x‖ ≤ b.R₀ + (b.L₁/b.μ)*R := by
  have hresp := P.primitive.response_distance_bound P.primitive.canonicalResponse x₀ x
  rw [norm_sub_rev x₀ x] at hresp
  have hcoef : 0 ≤ b.L₁/b.μ := div_nonneg b.L₁_pos.le b.μ_pos.le
  calc
    ‖y₀-P.yStar x‖ ≤ ‖y₀-P.yStar x₀‖ + ‖P.yStar x₀-P.yStar x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ b.R₀ + (b.L₁/b.μ)*‖x-x₀‖ := add_le_add hinit hresp
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hdistance hcoef) _

end Smoothness2601.InnerGeometry
