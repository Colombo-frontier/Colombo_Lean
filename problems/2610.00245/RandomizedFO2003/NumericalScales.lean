import RandomizedFO2003.CascadeFunctionClass
import Mathlib.Data.Real.Sqrt

namespace RandomizedFO2003.Cascade

noncomputable def curvatureDenominator : ℝ := 1 + cascadeSecondConstant + cascadeThirdConstant
noncomputable def curvatureCoefficient : ℝ := 1 / (8 * curvatureDenominator)
noncomputable def accuracyConstant : ℝ := 1 / (512 * 4096 ^ 2)

def rhsScale (ε : ℝ) : ℝ := 512 * ε
noncomputable def lowerCurvature (ε L₂ : ℝ) : ℝ :=
  curvatureCoefficient * Real.sqrt (L₂ * rhsScale ε)
noncomputable def upperCurvature (L₁ : ℝ) : ℝ := L₁ / 4

theorem curvatureDenominator_ge_one : 1 ≤ curvatureDenominator := by
  have h₂ := cascadeSecondConstant_pos
  have h₃ := cascadeThirdConstant_pos
  unfold curvatureDenominator
  linarith

theorem curvatureDenominator_pos : 0 < curvatureDenominator := lt_of_lt_of_le zero_lt_one curvatureDenominator_ge_one

theorem curvatureCoefficient_pos : 0 < curvatureCoefficient := by
  unfold curvatureCoefficient
  exact one_div_pos.mpr (mul_pos (by norm_num) curvatureDenominator_pos)

theorem curvatureCoefficient_product_bound {C : ℝ} (hC : C ≤ curvatureDenominator) :
    C * curvatureCoefficient ≤ 1 / 8 := by
  unfold curvatureCoefficient
  rw [mul_one_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) curvatureDenominator_pos)).mpr
  nlinarith only [hC]

theorem curvatureCoefficient_le_one : curvatureCoefficient ≤ 1 := by
  have hc := curvatureCoefficient_product_bound curvatureDenominator_ge_one
  linarith

theorem curvature_second_coefficient_bound : cascadeSecondConstant * curvatureCoefficient ≤ 1 / 8 := by
  apply curvatureCoefficient_product_bound
  unfold curvatureDenominator
  have h₃ := cascadeThirdConstant_pos
  linarith

theorem curvature_third_coefficient_bound : cascadeThirdConstant * curvatureCoefficient ^ 2 ≤ 1 := by
  have hc : cascadeThirdConstant * curvatureCoefficient ≤ 1 / 8 := by
    apply curvatureCoefficient_product_bound
    unfold curvatureDenominator
    have h₂ := cascadeSecondConstant_pos
    linarith
  calc
    _ = (cascadeThirdConstant * curvatureCoefficient) * curvatureCoefficient := by ring
    _ ≤ (1 / 8 : ℝ) * 1 := mul_le_mul hc curvatureCoefficient_le_one curvatureCoefficient_pos.le (by norm_num)
    _ ≤ 1 := by norm_num

theorem accuracyConstant_pos : 0 < accuracyConstant := by norm_num [accuracyConstant]

theorem rhsScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < rhsScale ε := by unfold rhsScale; positivity

theorem lowerCurvature_pos {ε L₂ : ℝ} (hε : 0 < ε) (hL₂ : 0 < L₂) : 0 < lowerCurvature ε L₂ :=
  mul_pos curvatureCoefficient_pos (Real.sqrt_pos.mpr (mul_pos hL₂ (rhsScale_pos hε)))

theorem upperCurvature_pos {L₁ : ℝ} (hL₁ : 0 < L₁) : 0 < upperCurvature L₁ := div_pos hL₁ (by norm_num)

/-- The high-accuracy hypothesis in the main target implies the numerical
separation needed by the later degree floor. -/
theorem accuracy_scale_bound {ε L₁ L₂ : ℝ} (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂) :
    L₂ * rhsScale ε ≤ (L₁ / 4096) ^ 2 := by
  have h := (le_div_iff₀ hL₂).mp haccuracy
  calc
    _ = 512 * (ε * L₂) := by unfold rhsScale; ring
    _ ≤ 512 * (accuracyConstant * L₁ ^ 2) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by unfold accuracyConstant; ring

theorem lowerCurvature_small {ε L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂) :
    lowerCurvature ε L₂ ≤ L₁ / 4096 := by
  have hs := (Real.sqrt_le_left (by positivity : 0 ≤ L₁ / 4096)).mpr
    (accuracy_scale_bound hL₂ haccuracy)
  exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) curvatureCoefficient_le_one).trans hs

theorem spectral_interval_separation {ε L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂) :
    2 * lowerCurvature ε L₂ ≤ upperCurvature L₁ := by
  have hc := lowerCurvature_small hL₁ hL₂ haccuracy
  unfold upperCurvature
  linarith

/-- The complete second-derivative budget follows from the fixed numerical
coefficient and the main high-accuracy hypothesis. -/
theorem chosen_second_budget {ε L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂) :
    upperCurvature L₁ + cascadeSecondConstant * lowerCurvature ε L₂ ≤ L₁ := by
  have hs : Real.sqrt (L₂ * rhsScale ε) ≤ L₁ := by
    apply (Real.sqrt_le_left hL₁.le).mpr
    have h := accuracy_scale_bound hL₂ haccuracy
    nlinarith [sq_nonneg L₁]
  have hc : cascadeSecondConstant * lowerCurvature ε L₂ ≤ (1 / 8 : ℝ) * L₁ := by
    unfold lowerCurvature
    rw [← mul_assoc]
    exact mul_le_mul curvature_second_coefficient_bound hs (Real.sqrt_nonneg _) (by norm_num)
  unfold upperCurvature
  linarith

theorem chosen_third_budget {ε L₂ : ℝ} (hε : 0 < ε) (hL₂ : 0 < L₂) :
    cascadeThirdConstant * (lowerCurvature ε L₂) ^ 2 / rhsScale ε ≤ L₂ := by
  have hh := rhsScale_pos hε
  calc
    _ = (cascadeThirdConstant * curvatureCoefficient ^ 2) * L₂ := by
      unfold lowerCurvature
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hL₂.le hh.le)]
      field_simp
      ring
    _ ≤ 1 * L₂ := mul_le_mul_of_nonneg_right curvature_third_coefficient_bound hL₂.le
    _ = L₂ := one_mul _

end RandomizedFO2003.Cascade
