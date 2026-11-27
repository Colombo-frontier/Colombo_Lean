import Nonsmooth.CircularNeighborLiftGeometry
import Mathlib.Algebra.Order.Field.GeomSum

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def circularRadiusRatio (ε : ℝ) (N : ℕ) : ℝ := ε * Real.sin (circularGridAngle N) / 8

def shrinkingCircularRadius (R ε : ℝ) (N i : ℕ) : ℝ :=
  (R / 8) * (circularRadiusRatio ε N) ^ i

theorem circularRadiusRatio_pos {ε : ℝ} (hε : 0 < ε) (N : ℕ) : 0 < circularRadiusRatio ε N :=
  div_pos (mul_pos hε (circularGridAngle_sin_pos N)) (by norm_num)

theorem circularRadiusRatio_le_half {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (N : ℕ) :
    circularRadiusRatio ε N ≤ 1 / 2 := by
  have hs := Real.sin_le_one (circularGridAngle N)
  have hm := mul_le_mul_of_nonneg_left hs hε
  dsimp [circularRadiusRatio]
  nlinarith

theorem shrinkingCircularRadius_pos {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (N i : ℕ) :
    0 < shrinkingCircularRadius R ε N i :=
  mul_pos (div_pos hR (by norm_num)) (pow_pos (circularRadiusRatio_pos hε N) i)

variable {E : Type} [NormedAddCommGroup E]

theorem geometric_path_displacement (y : ℕ → E) {r β : ℝ} (hr : 0 ≤ r)
    (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2) (D m : ℕ) (hm : m ≤ D)
    (hstep : ∀ i < D, ‖y (i + 1) - y i‖ ≤ 2 * r * β ^ i) :
    ‖y D - y m‖ ≤ 4 * r * β ^ m := by
  have hlt : β < 1 := by linarith
  have hd : dist (y m) (y D) ≤ ∑ i ∈ Finset.Ico m D, 2 * r * β ^ i := by
    apply dist_le_Ico_sum_of_dist_le hm
    intro i _ hi
    have hh := hstep i hi
    simpa only [dist_eq_norm, norm_sub_rev] using hh
  have hg := geom_sum_Ico_le_of_lt_one hβ hlt (m := m) (n := D)
  have hg' := mul_le_mul_of_nonneg_left hg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)
  have hpow : 0 ≤ β ^ m := pow_nonneg hβ m
  have hdiv : β ^ m / (1 - β) ≤ 2 * β ^ m := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - β)).mpr
    nlinarith [mul_nonneg hpow (sub_nonneg.mpr hβhalf)]
  have hdiv' := mul_le_mul_of_nonneg_left hdiv (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)
  rw [← Finset.mul_sum] at hd
  have hdist : dist (y m) (y D) = ‖y D - y m‖ := by rw [dist_comm, dist_eq_norm]
  rw [hdist] at hd
  nlinarith only [hd, hg', hdiv']

theorem shrinkingCircularRadius_tail (y : ℕ → E) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) (N D i : ℕ) (hi : i < D)
    (hstep : ∀ j < D, ‖y (j + 1) - y j‖ ≤ 2 * shrinkingCircularRadius R ε N j) :
    ‖y D - y (i + 1)‖ ≤
      (shrinkingCircularRadius R ε N i * Real.sin (circularGridAngle N)) * (ε / 2) := by
  have h := geometric_path_displacement (r := R / 8) y (div_nonneg hR (by norm_num))
    (circularRadiusRatio_pos hε N).le (circularRadiusRatio_le_half hε.le hε1 N) D (i + 1)
    (by omega) (fun j hj => by simpa only [shrinkingCircularRadius, mul_assoc] using hstep j hj)
  calc
    _ ≤ 4 * (R / 8) * (circularRadiusRatio ε N) ^ (i + 1) := h
    _ = _ := by
      rw [pow_succ]
      dsimp only [shrinkingCircularRadius, circularRadiusRatio]
      ring

theorem shrinkingCircularRadius_path_bound (y : ℕ → E) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) (N D : ℕ) (hy0 : y 0 = 0)
    (hstep : ∀ j < D, ‖y (j + 1) - y j‖ ≤ 2 * shrinkingCircularRadius R ε N j) :
    ‖y D‖ ≤ R / 2 := by
  have h := geometric_path_displacement (r := R / 8) y (div_nonneg hR (by norm_num))
    (circularRadiusRatio_pos hε N).le (circularRadiusRatio_le_half hε.le hε1 N) D 0 (Nat.zero_le D)
    (fun j hj => by simpa only [shrinkingCircularRadius, mul_assoc] using hstep j hj)
  rw [hy0, sub_zero, pow_zero, mul_one] at h
  linarith

end
end Nonsmooth
