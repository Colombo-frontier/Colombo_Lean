import GaussianMetric254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

theorem rotatedPrecision_one {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) :
    rotatedPrecision U (fun _ => 1) = 1 := by
  simp only [rotatedPrecision, Matrix.diagonal_one, Matrix.mul_one,
    ← star_eq_conjTranspose, unitary.coe_star_mul_self]

theorem unitary_sum_squares {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (x : Coordinates d) : ∑ j, ((U : Precision d) *ᵥ x) j^2 = ∑ j, x j^2 := by
  have hh := rotatedPrecision_quadratic U (fun _ => 1) x
  rw [rotatedPrecision_one] at hh
  simpa only [matrixQuadratic, Matrix.one_mulVec, dotProduct, one_mul, pow_two] using hh.symm

theorem rotatedPrecision_quadratic_bound {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (b : ℝ) (hc : ∀ j, c j ≤ b) (x : Space d) :
    matrixQuadratic (rotatedPrecision U c) x ≤ b*‖x‖^2 := by
  rw [rotatedPrecision_quadratic]
  calc
    _ ≤ ∑ j, b*((U : Precision d) *ᵥ x) j^2 :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _))
    _ = b*(∑ j, x j^2) := by rw [← Finset.mul_sum, unitary_sum_squares]
    _ = _ := by simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

theorem PrecisionGaussian.floor_quadratic_bound {d : ℕ} (P : PrecisionGaussian d)
    (q : ℝ) (hq : 0 < q) (x : Space d) :
    matrixQuadratic (P.floorCovariance q hq).precision x ≤ (1/q)*‖x‖^2 := by
  exact rotatedPrecision_quadratic_bound _ _ _ (fun _ => min_le_right _ _) x

theorem PrecisionGaussian.floor_factor_bound {d : ℕ} (P : PrecisionGaussian d)
    (q : ℝ) (hq : 0 < q) (x : Space d) :
    ‖precisionFactor (P.floorCovariance q hq).positive x‖ ≤ (1/Real.sqrt q)*‖x‖ := by
  have hh := P.floor_quadratic_bound q hq x
  rw [← precisionFactor_norm (P.floorCovariance q hq).positive] at hh
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  have he : ((1/Real.sqrt q)*‖x‖)^2 = (1/q)*‖x‖^2 := by
    rw [mul_pow, div_pow, one_pow, hs2]
  have hn : 0 ≤ (1/Real.sqrt q)*‖x‖ := by positivity
  nlinarith [norm_nonneg (precisionFactor (P.floorCovariance q hq).positive x)]

end Paper254
#print axioms Paper254.PrecisionGaussian.floor_factor_bound
