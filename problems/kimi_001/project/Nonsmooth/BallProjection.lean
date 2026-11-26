import Nonsmooth.Geometry

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
open scoped Classical
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ballProject (ρ : ℝ) (x : E) : E := if ‖x‖ ≤ ρ then x else (ρ / ‖x‖) • x

theorem ballProject_fixed {ρ : ℝ} {x : E} (hx : ‖x‖ ≤ ρ) : ballProject ρ x = x := if_pos hx

theorem ballProject_feasible {ρ : ℝ} (hρ : 0 ≤ ρ) (x : E) : ‖ballProject ρ x‖ ≤ ρ := by
  by_cases hx : ‖x‖ ≤ ρ
  · rwa [ballProject_fixed hx]
  · have hn : 0 < ‖x‖ := by linarith
    rw [ballProject, if_neg hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ hn.le),
      div_mul_cancel₀ _ hn.ne']

/-- The Euclidean variational inequality for the explicit radial projection. -/
theorem ballProject_variational {ρ : ℝ} (hρ : 0 ≤ ρ) (x : E) {z : E} (hz : ‖z‖ ≤ ρ) :
    inner ℝ (x - ballProject ρ x) (z - ballProject ρ x) ≤ (0 : ℝ) := by
  by_cases hx : ‖x‖ ≤ ρ
  · simp [ballProject_fixed hx]
  · have hn : 0 < ‖x‖ := by linarith
    have ht : 0 ≤ 1 - ρ / ‖x‖ := by
      rw [le_sub_iff_add_le, zero_add]
      exact (div_le_one hn).mpr (by linarith)
    have hip : inner ℝ x z ≤ ‖x‖ * ρ :=
      (real_inner_le_norm x z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
    rw [ballProject, if_neg hx]
    have heq : inner ℝ (x - (ρ / ‖x‖) • x) (z - (ρ / ‖x‖) • x) =
        (1 - ρ / ‖x‖) * (inner ℝ x z - ‖x‖ * ρ) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp <;> ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr hip)

theorem ballProject_lipschitz {ρ : ℝ} (hρ : 0 ≤ ρ) : LipschitzWith 1 (ballProject (E := E) ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := ballProject_variational hρ x (ballProject_feasible hρ y)
  have hy := ballProject_variational hρ y (ballProject_feasible hρ x)
  have heq : ‖ballProject ρ x - ballProject ρ y‖ ^ 2 -
      inner ℝ (ballProject ρ x - ballProject ρ y) (x - y) =
      inner ℝ (x - ballProject ρ x) (ballProject ρ y - ballProject ρ x) +
      inner ℝ (y - ballProject ρ y) (ballProject ρ x - ballProject ρ y) := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm x (ballProject ρ y), real_inner_comm x (ballProject ρ x),
      real_inner_comm y (ballProject ρ x), real_inner_comm y (ballProject ρ y),
      real_inner_comm (ballProject ρ y) (ballProject ρ x)]
    ring
  have hsq : ‖ballProject ρ x - ballProject ρ y‖ ^ 2 ≤
      ‖ballProject ρ x - ballProject ρ y‖ * ‖x - y‖ := by
    have hc := real_inner_le_norm (ballProject ρ x - ballProject ρ y) (x - y)
    linarith
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  by_cases hzero : ballProject ρ x - ballProject ρ y = 0
  · simp [hzero]
  · have hp : 0 < ‖ballProject ρ x - ballProject ρ y‖ := norm_pos_iff.mpr hzero
    rw [pow_two] at hsq
    exact (mul_le_mul_iff_of_pos_left hp).mp hsq

theorem ballProject_comparator {ρ : ℝ} (hρ : 0 ≤ ρ) (x : E) {z : E} (hz : ‖z‖ ≤ ρ) :
    ‖ballProject ρ x - z‖ ≤ ‖x - z‖ := by
  have h := (ballProject_lipschitz hρ).dist_le_mul x z
  simpa only [ballProject_fixed hz, NNReal.coe_one, one_mul, dist_eq_norm] using h

/-- The exact pathwise distance recursion used by projected stochastic methods. -/
theorem projected_step_distance {ρ : ℝ} (hρ : 0 ≤ ρ) (η : ℝ) (x G : E) {z : E} (hz : ‖z‖ ≤ ρ) :
    ‖ballProject ρ (x - η • G) - z‖ ^ 2 ≤
      ‖x - z‖ ^ 2 - 2 * η * inner ℝ G (x - z) + η ^ 2 * ‖G‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (ballProject_comparator hρ (x - η • G) hz) 2
  have heq : x - η • G - z = (x - z) - η • G := by abel
  rw [heq, norm_sub_sq_real (x - z) (η • G), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right] at h
  rw [real_inner_comm] at h
  nlinarith [h]

end
end Nonsmooth
