import Nonsmooth.CircularConeGeometry
import Nonsmooth.TwoQueryOutwardCone

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem circularGridAngle_pos (N : ℕ) : 0 < circularGridAngle N := by
  unfold circularGridAngle
  positivity

theorem circularGridAngle_le_pi_div_two (N : ℕ) : circularGridAngle N ≤ Real.pi / 2 := by
  have hp : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  unfold circularGridAngle
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ N)).mpr
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hp)]

theorem circularGridAngle_sin_pos (N : ℕ) : 0 < Real.sin (circularGridAngle N) := by
  apply Real.sin_pos_of_pos_of_lt_pi (circularGridAngle_pos N)
  have h := circularGridAngle_le_pi_div_two N
  linarith [Real.pi_pos]

theorem circularGridAngle_cos_gap_pos (N : ℕ) : 0 < 1 - Real.cos (circularGridAngle N) := by
  have hs := circularGridAngle_sin_pos N
  have hid := Real.sin_sq_add_cos_sq (circularGridAngle N)
  have hc := Real.cos_le_one (circularGridAngle N)
  nlinarith [sq_pos_of_pos hs]

theorem nonnegative_two_ray_coefficients {r D S h t : ℝ}
    (hr : 0 < r) (hD : 0 < D) (hS : 0 < S) (hcone : D * |t| ≤ S * h) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ r * D * (a + b) = h ∧ r * S * (a - b) = t := by
  have hrD : 0 < r * D := mul_pos hr hD
  have hrS : 0 < r * S := mul_pos hr hS
  have hquot : |t / (r * S)| ≤ h / (r * D) := by
    rw [abs_div, abs_of_pos hrS, div_le_div_iff₀ hrS hrD]
    convert mul_le_mul_of_nonneg_left hcone hr.le using 1 <;> ring
  refine ⟨(h / (r * D) + t / (r * S)) / 2,
    (h / (r * D) - t / (r * S)) / 2, ?_, ?_, ?_, ?_⟩
  · have hl := neg_abs_le (t / (r * S))
    linarith
  · have hl := le_abs_self (t / (r * S))
    linarith
  · field_simp
    ring
  · field_simp
    ring

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem circular_query_cone_contains_sector (o u v : E) {r : ℝ} (hr : 0 < r)
    (N : ℕ) (j : ℤ) {h t : ℝ}
    (hcone : (1 - Real.cos (circularGridAngle N)) * |t| ≤ Real.sin (circularGridAngle N) * h) :
    circularQueryPoint o u v r N j +
      h • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) +
      t • circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) ∈
    finiteComparisonCone ![circularQueryPoint o u v r N (j - 1),
      circularQueryPoint o u v r N (j + 1)] (circularQueryPoint o u v r N j) := by
  obtain ⟨a, b, ha, hb, hrad, htan⟩ := nonnegative_two_ray_coefficients hr
    (circularGridAngle_cos_gap_pos N) (circularGridAngle_sin_pos N) hcone
  have hm := two_query_outward_cone_mem
    ![circularQueryPoint o u v r N (j - 1), circularQueryPoint o u v r N (j + 1)]
    (circularQueryPoint o u v r N j) ha hb
  have he := circular_query_cone_coordinates o u v r N j a b
  rw [hrad, htan] at he
  exact he ▸ hm

end
end Nonsmooth
