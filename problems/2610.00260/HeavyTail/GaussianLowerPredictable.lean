import HeavyTail.GaussianLowerLikelihood
import Mathlib.MeasureTheory.Integral.Prod

/-! Fresh Gaussian likelihood increments with a direction chosen measurably
from the past. The mean identity and second-moment recurrence are proved by
Fubini, without an assumed conditional-information inequality. -/

open MeasureTheory
open scoped InnerProductSpace
namespace HeavyTail.GaussianLower
noncomputable section

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma exponentialRatio_measurable :
    Measurable (fun v : E × E ↦ exponentialRatio v.1 v.2) := by
  unfold exponentialRatio
  fun_prop

def likelihoodStep (W : Ω → ℝ) (d : Ω → E) (ω : Ω × E) : ℝ :=
  W ω.1 * exponentialRatio (d ω.1) ω.2

lemma likelihoodStep_measurable {W : Ω → ℝ} {d : Ω → E}
    (hW : Measurable W) (hd : Measurable d) : Measurable (likelihoodStep W d) := by
  unfold likelihoodStep exponentialRatio
  fun_prop

omit [IsProbabilityMeasure P] in
theorem likelihoodStep_integrable {W : Ω → ℝ} {d : Ω → E}
    (hW : Measurable W) (hd : Measurable d) (hWi : Integrable W P) :
    Integrable (likelihoodStep W d) (P.prod (GaussianEstimates.euclideanGaussianLaw E)) := by
  apply (integrable_prod_iff (likelihoodStep_measurable hW hd).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun ω ↦
      (exponentialRatio_integrable E (d ω)).const_mul (W ω)
  · have he (ω : Ω) : (∫ z, ‖likelihoodStep W d (ω, z)‖
          ∂GaussianEstimates.euclideanGaussianLaw E) = |W ω| := by
      simp only [likelihoodStep, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _), exponentialRatio]
      rw [integral_const_mul]
      change |W ω| * (∫ z, exponentialRatio (d ω) z
        ∂GaussianEstimates.euclideanGaussianLaw E) = |W ω|
      rw [exponentialRatio_mean, mul_one]
    simp_rw [he]
    exact hWi.abs

theorem likelihoodStep_mean {W : Ω → ℝ} {d : Ω → E}
    (hW : Measurable W) (hd : Measurable d) (hWi : Integrable W P) :
    (∫ ω, likelihoodStep W d ω ∂P.prod (GaussianEstimates.euclideanGaussianLaw E)) =
      ∫ ω, W ω ∂P := by
  rw [integral_prod _ (likelihoodStep_integrable hW hd hWi)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ by
    simp only [likelihoodStep]
    rw [integral_const_mul, exponentialRatio_mean, mul_one]

omit [IsProbabilityMeasure P] in
theorem likelihoodStep_square_integrable {W : Ω → ℝ} {d : Ω → E} {C : ℝ}
    (hW : Measurable W) (hd : Measurable d) (hWi : Integrable (fun ω ↦ W ω ^ 2) P)
    (hbound : ∀ ω, ‖d ω‖ ^ 2 ≤ C) :
    Integrable (fun ω ↦ likelihoodStep W d ω ^ 2)
      (P.prod (GaussianEstimates.euclideanGaussianLaw E)) := by
  have ho : Integrable (fun ω ↦ W ω ^ 2 * Real.exp (‖d ω‖ ^ 2)) P := by
    apply (hWi.mul_const (Real.exp C)).mono'
    · exact ((hW.pow_const 2).mul ((hd.norm.pow_const 2).exp)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbound ω)) (sq_nonneg _)
  apply (integrable_prod_iff ((likelihoodStep_measurable hW hd).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun ω ↦ by
      simpa only [likelihoodStep, mul_pow] using
        (exponentialRatio_square_integrable E (d ω)).const_mul (W ω ^ 2)
  · have he (ω : Ω) : (∫ z, ‖likelihoodStep W d (ω, z) ^ 2‖
          ∂GaussianEstimates.euclideanGaussianLaw E) = W ω ^ 2 * Real.exp (‖d ω‖ ^ 2) := by
      simp only [Real.norm_eq_abs, likelihoodStep, mul_pow, abs_mul, abs_pow, sq_abs]
      rw [integral_const_mul, exponentialRatio_second]
    simpa only [he] using ho

theorem likelihoodStep_second_le {W : Ω → ℝ} {d : Ω → E} {C : ℝ}
    (hW : Measurable W) (hd : Measurable d) (hWi : Integrable (fun ω ↦ W ω ^ 2) P)
    (hbound : ∀ ω, ‖d ω‖ ^ 2 ≤ C) :
    (∫ ω, likelihoodStep W d ω ^ 2 ∂P.prod (GaussianEstimates.euclideanGaussianLaw E)) ≤
      Real.exp C * (∫ ω, W ω ^ 2 ∂P) := by
  have hi := likelihoodStep_square_integrable hW hd hWi hbound
  rw [integral_prod _ hi]
  have he (ω : Ω) : (∫ z, likelihoodStep W d (ω, z) ^ 2
          ∂GaussianEstimates.euclideanGaussianLaw E) = W ω ^ 2 * Real.exp (‖d ω‖ ^ 2) := by
    simp only [likelihoodStep, mul_pow]
    rw [integral_const_mul, exponentialRatio_second]
  simp_rw [he]
  rw [← integral_const_mul]
  apply integral_mono
  · simpa only [he] using hi.integral_prod_left
  · exact hWi.const_mul _
  · intro ω
    simpa only [mul_comm (Real.exp C)] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbound ω)) (sq_nonneg (W ω))

end
end HeavyTail.GaussianLower
