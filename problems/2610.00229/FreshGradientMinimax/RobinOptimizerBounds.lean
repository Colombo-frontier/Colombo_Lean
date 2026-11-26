import FreshGradientMinimax.RobinEdgeEnergy
import FreshGradientMinimax.SparsePairNorm

/-! Original coordinate and Euclidean norm bounds for the exact quadratic
optimizer of each dual subchain. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robin_sqrt_C_bound {n : ℕ} (hn : 10 ≤ n) : Real.sqrt (robinC n) ≤ 28 / 3 := by
  have hC := robin_coefficients_bounds hn
  have h0 : 0 ≤ robinC n := le_trans (by norm_num) hC.1
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (robinC n)]

theorem robin_source_scale_mul_dimension {n : ℕ} (hn : 10 ≤ n + 2) :
    Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) * (n + 2 : ℕ) =
      Real.sqrt (robinC (n + 2)) * Real.sqrt (n + 2 : ℕ) := by
  have hC : 0 ≤ robinC (n + 2) := le_trans (by norm_num) (robin_coefficients_bounds hn).1
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hs := (Real.sqrt_pos.mpr hN).ne'
  rw [Real.sqrt_div hC]
  calc
    _ = Real.sqrt (robinC (n + 2)) / Real.sqrt (n + 2 : ℕ) *
        (Real.sqrt (n + 2 : ℕ) * Real.sqrt (n + 2 : ℕ)) := by rw [← pow_two, Real.sq_sqrt hN.le]
    _ = _ := by
      field_simp
      rw [mul_assoc, Real.mul_self_sqrt (by positivity)]

theorem robin_optimizer_coordinate_bound {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) (i : Fin (n + 2)) :
    |robinQuadraticOptimizer n a b i| ≤ 42 * Real.sqrt (n + 2 : ℕ) := by
  have hF := robinInverse_first_bounds hn i
  have hL := robinInverse_last_bounds hn i
  have hFabs : |robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i| ≤ (n + 2 : ℕ) := by
    rw [abs_of_pos hF.1]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hF.2.le
  have hLabs : |robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i| ≤ (n + 2 : ℕ) := by
    rw [abs_of_pos hL.1]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hL.2.le
  have haF := mul_le_mul ha hFabs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  have hbL := mul_le_mul hb hLabs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have htri := abs_sub
    (a * robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i)
    (b * robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i)
  rw [abs_mul, abs_mul] at htri
  have hsum : |a * robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i -
      b * robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i| ≤
      (9 / 2) * (n + 2 : ℕ) := by linarith only [htri, haF, hbL]
  simp only [robinQuadraticOptimizer, robinQuadraticSource, robinEndpointSource, map_smul,
    map_sub, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) * ((9 / 2) * (n + 2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = (9 / 2) * Real.sqrt (robinC (n + 2)) * Real.sqrt (n + 2 : ℕ) := by
      nlinarith only [robin_source_scale_mul_dimension hn]
    _ ≤ 42 * Real.sqrt (n + 2 : ℕ) := by
      have h := mul_le_mul_of_nonneg_right (robin_sqrt_C_bound hn) (Real.sqrt_nonneg (n + 2 : ℕ))
      nlinarith only [h]

theorem robin_optimizer_norm_bound {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) :
    ‖robinQuadraticOptimizer n a b‖ ≤ 42 * (n + 2 : ℕ) := by
  have h := euclid_norm_le_of_coordinate_bound (robinQuadraticOptimizer n a b)
    (by positivity : 0 ≤ 42 * Real.sqrt (n + 2 : ℕ)) (robin_optimizer_coordinate_bound hn ha hb)
  simpa only [mul_assoc, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg (n + 2))] using h

end FreshGradientMinimax
