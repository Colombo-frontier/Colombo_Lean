import HeavyTail.MaskedCoordinateOracle
import HeavyTail.MaskedMomentTools

/-! Raw moments of the finite coordinate-revelation sampler. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace HeavyTail.MaskedLower
noncomputable section

theorem coordinateReply_norm_moment_le {k : ℕ} {π p b : ℝ} (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (hp : 0 < p) (hb : 0 ≤ b)
    (g : HardSpace k) (hg : ∀ j, |g j| ≤ b) :
    (∫ m, ‖coordinateReply π g m‖ ^ p ∂(coordinateCoin π hπ.le hkπ).toMeasure) ≤
      ((k : ℝ) * π) * (b / π) ^ p := by
  rw [coordinate_expectation]
  simp only [coordinateReply, norm_zero, Real.zero_rpow hp.ne', smul_eq_mul, mul_zero, zero_add,
    EuclideanSpace.norm_single, Real.norm_eq_abs]
  calc
    _ ≤ ∑ _j : Fin k, π * (b / π) ^ p := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ hπ.le
      rw [abs_div, abs_of_pos hπ]
      exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right (hg j) hπ.le) hp.le
    _ = _ := by simp; ring

theorem coordinateReply_direction_moment_le {k : ℕ} (hk : 0 < k) {π p b : ℝ}
    (hπ : 0 < π) (hkπ : (k : ℝ) * π ≤ 1) (hp : 0 < p) (hp2 : p ≤ 2) (hb : 0 ≤ b)
    (g : HardSpace k) (hg : ∀ j, |g j| ≤ b) (w : HardSpace k) (hw : ‖w‖ = 1) :
    (∫ m, |⟪w, coordinateReply π g m⟫_ℝ| ^ p ∂(coordinateCoin π hπ.le hkπ).toMeasure) ≤
      ((k : ℝ) * π) * ((b / π) * (1 / Real.sqrt k)) ^ p := by
  have hj (j : Fin k) : |⟪w, EuclideanSpace.single j (g j / π)⟫_ℝ| ^ p ≤
      (b / π) ^ p * |w j| ^ p := by
    rw [EuclideanSpace.inner_single_right]
    simp only [conj_trivial, abs_mul]
    rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg _) _)
    rw [abs_div, abs_of_pos hπ]
    exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right (hg j) hπ.le) hp.le
  rw [coordinate_expectation]
  simp only [coordinateReply, inner_zero_right, abs_zero, Real.zero_rpow hp.ne',
    smul_eq_mul, mul_zero, zero_add]
  calc
    _ ≤ ∑ j : Fin k, π * ((b / π) ^ p * |w j| ^ p) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj j) hπ.le
    _ = π * (b / π) ^ p * ∑ j : Fin k, |w j| ^ p := by
      simp only [← Finset.mul_sum, mul_assoc]
    _ ≤ π * (b / π) ^ p * ((k : ℝ) * (1 / Real.sqrt k) ^ p) :=
      mul_le_mul_of_nonneg_left (coordinate_lp_sum_bound hk hp.le hp2 w hw) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

end
end HeavyTail.MaskedLower
