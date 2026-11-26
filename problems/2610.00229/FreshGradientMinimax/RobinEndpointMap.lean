import FreshGradientMinimax.RobinEdgeEnergy
import FreshGradientMinimax.RobinOptimizerBounds
import FreshGradientMinimax.EuclidDropLast

/-! The concrete primal endpoint map (a,z) ↦ shift(a,z/2). -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def robinEndpointMap (n : ℕ) : Euclid 2 →L[ℝ] Euclid (n + 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => robinEdgeShift n (x 0) (x 1 / 2)
      map_add' := by
        intro x y
        ext e
        simp only [robinEdgeShift, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
        ring
      map_smul' := by
        intro a x
        ext e
        simp only [robinEdgeShift, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, RingHom.id_apply]
        ring }

theorem robinEndpointMap_apply (n : ℕ) (x : Euclid 2) :
    robinEndpointMap n x = robinEdgeShift n (x 0) (x 1 / 2) := rfl

theorem robinEndpointMap_norm_sq {n : ℕ} (hn : 10 ≤ n + 2) (x : Euclid 2) :
    ‖robinEndpointMap n x‖ ^ 2 = robinC (n + 2) * (x 0 ^ 2 + x 1 ^ 2 / 4) := by
  rw [robinEndpointMap_apply, robinEdgeShift_norm_sq hn]
  ring

theorem robinEndpointMap_norm {n : ℕ} (hn : 10 ≤ n + 2) (x : Euclid 2) :
    ‖robinEndpointMap n x‖ ≤ Real.sqrt (robinC (n + 2)) * ‖x‖ := by
  have hC : 0 ≤ robinC (n + 2) := le_trans (by norm_num) (robin_coefficients_bounds hn).1
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [robinEndpointMap_norm_sq hn, mul_pow, Real.sq_sqrt hC, euclid_norm_sq, Fin.sum_univ_two]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (x 1)]) hC

theorem robinEndpointMap_opNorm {n : ℕ} (hn : 10 ≤ n + 2) :
    ‖robinEndpointMap n‖ ≤ Real.sqrt (robinC (n + 2)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (robinEndpointMap_norm hn)

theorem robinEndpointMap_single_zero (n : ℕ) :
    robinEndpointMap n (EuclideanSpace.single 0 1) =
      -Real.sqrt (robinC (n + 2)) • EuclideanSpace.single 0 1 := by
  simp [robinEndpointMap_apply, robinEdgeShift, EuclideanSpace.single_apply]

theorem robinEndpointMap_single_one (n : ℕ) :
    robinEndpointMap n (EuclideanSpace.single 1 1) =
      -(Real.sqrt (robinC (n + 2)) / 2) • EuclideanSpace.single (Fin.last (n + 2)) 1 := by
  simp only [robinEndpointMap_apply, robinEdgeShift, EuclideanSpace.single_apply,
    show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, if_false, if_true,
    zero_smul, zero_add, smul_smul]
  congr 1
  ring

theorem robinEndpointMap_adjoint_zero (n : ℕ) (w : Euclid (n + 3)) :
    ((robinEndpointMap n)†) w 0 = -Real.sqrt (robinC (n + 2)) * w 0 := by
  have h := (robinEndpointMap n).adjoint_inner_left (EuclideanSpace.single 0 1) w
  simpa [robinEndpointMap_single_zero, EuclideanSpace.inner_single_right, real_inner_smul_right] using h

theorem robinEndpointMap_adjoint_one (n : ℕ) (w : Euclid (n + 3)) :
    ((robinEndpointMap n)†) w 1 = -(Real.sqrt (robinC (n + 2)) / 2) * w (Fin.last (n + 2)) := by
  have h := (robinEndpointMap n).adjoint_inner_left (EuclideanSpace.single 1 1) w
  simpa [robinEndpointMap_single_one, EuclideanSpace.inner_single_right, real_inner_smul_right] using h

theorem robinEndpointMap_adjoint_coordinate {n : ℕ} (hn : 10 ≤ n + 2) {B : ℝ}
    (_hB : 0 ≤ B) (w : Euclid (n + 3)) (hw : ∀ e, |w e| ≤ B) (i : Fin 2) :
    |((robinEndpointMap n)†) w i| ≤ (28 / 3) * B := by
  fin_cases i
  · change |((robinEndpointMap n)†) w 0| ≤ _
    rw [robinEndpointMap_adjoint_zero, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (robin_sqrt_C_bound hn) (hw 0) (abs_nonneg _) (by norm_num)
  · change |((robinEndpointMap n)†) w 1| ≤ _
    rw [robinEndpointMap_adjoint_one, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    have h := mul_le_mul (robin_sqrt_C_bound hn) (hw (Fin.last (n + 2))) (abs_nonneg _) (by norm_num)
    nlinarith only [h, mul_nonneg (Real.sqrt_nonneg (robinC (n + 2))) (abs_nonneg (w (Fin.last (n + 2))))]

theorem robinEndpointMap_adjoint_bounded_norm {n : ℕ} (hn : 10 ≤ n + 2) {B : ℝ}
    (hB : 0 ≤ B) (w : Euclid (n + 3)) (hw : ∀ e, |w e| ≤ B) :
    ‖((robinEndpointMap n)†) w‖ ≤ 11 * B := by
  have hC := robin_coefficients_bounds hn
  have hC0 : 0 ≤ robinC (n + 2) := le_trans (by norm_num) hC.1
  have h0 : w 0 ^ 2 ≤ B ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw 0) 2
  have h1 : w (Fin.last (n + 2)) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw (Fin.last (n + 2))) 2
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [euclid_norm_sq, Fin.sum_univ_two, robinEndpointMap_adjoint_zero, robinEndpointMap_adjoint_one]
  simp only [mul_pow, neg_sq, div_pow, Real.sq_sqrt hC0]
  have hh := mul_le_mul_of_nonneg_left (show w 0 ^ 2 + w (Fin.last (n + 2)) ^ 2 / 4 ≤ (5 / 4) * B ^ 2 by linarith) hC0
  have hc := mul_le_mul_of_nonneg_right hC.2.1 (show 0 ≤ (5 / 4) * B ^ 2 by positivity)
  nlinarith only [hh, hc, sq_nonneg B]

end FreshGradientMinimax
