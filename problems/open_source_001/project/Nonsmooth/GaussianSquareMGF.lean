import Nonsmooth.GaussianCharacteristic

open MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem standardGaussian_square_exponential_integral {t : ℝ} (ht : t < 1 / 2) :
    (∫ z : ℝ, Real.exp (t * z ^ 2) ∂gaussianReal 0 1) = (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  have hc : 0 < 1 - 2 * t := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have he (z : ℝ) : gaussianPDFReal 0 1 z • Real.exp (t * z ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * z ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian]
  calc
    _ = Real.sqrt (Real.pi / (1 / 2 - t)) / Real.sqrt (2 * Real.pi) := by ring
    _ = Real.sqrt ((Real.pi / (1 / 2 - t)) / (2 * Real.pi)) :=
      (Real.sqrt_div (div_nonneg Real.pi_pos.le hb.le) _).symm
    _ = Real.sqrt ((1 - 2 * t)⁻¹) := by
      congr 1
      field_simp
    _ = _ := Real.sqrt_inv _

theorem standardGaussian_square_exponential_integrable {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : ℝ => Real.exp (t * z ^ 2)) (gaussianReal 0 1) := by
  by_contra h
  have hi := standardGaussian_square_exponential_integral ht
  rw [integral_undef h] at hi
  have hp : 0 < (Real.sqrt (1 - 2 * t))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  linarith

theorem standardGaussianCoordinates_square_exponential (d : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    (∫ v : Fin d → ℝ, Real.exp (t * ∑ i, (v i) ^ 2) ∂standardGaussianCoordinates d) =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ d := by
  have he (v : Fin d → ℝ) : Real.exp (t * ∑ i, (v i) ^ 2) = ∏ i, Real.exp (t * (v i) ^ 2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [he]
  have hi : (∫ v : Fin d → ℝ, ∏ i, Real.exp (t * (v i) ^ 2) ∂standardGaussianCoordinates d) =
      ∏ _i : Fin d, ∫ z : ℝ, Real.exp (t * z ^ 2) ∂gaussianReal 0 1 := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
    letI : SigmaFinite (volume : Measure ℝ) := by
      change SigmaFinite (gaussianReal 0 1)
      infer_instance
    exact integral_fintype_prod_eq_prod (fun (_ : Fin d) (z : ℝ) => Real.exp (t * z ^ 2))
  rw [hi]
  simp only [standardGaussian_square_exponential_integral ht, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end
end Nonsmooth
