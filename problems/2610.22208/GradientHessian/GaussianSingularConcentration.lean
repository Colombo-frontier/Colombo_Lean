import GradientHessian.GaussianMeanTails
import GradientHessian.GaussianSingularGeometry

/-! The exact one-sided concentration step for the largest and least
expansion of an actual contractive linear Gaussian operator family. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ H]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ H]
  [FiniteDimensional ℝ E] [Nontrivial E] in
theorem contraction_lipschitz (A : H →L[ℝ] (E →L[ℝ] F)) (hA : ‖A‖ ≤ 1) : LipschitzWith 1 A := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,← map_sub]
  exact (A.le_opNorm (x-y)).trans (by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hA (norm_nonneg (x-y))))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem gaussian_largestExpansion_tail (A : H →L[ℝ] (E →L[ℝ] F)) (hA : ‖A‖ ≤ 1)
    {c t : ℝ} (hc : (∫ z, ‖A z‖ ∂euclideanGaussianLaw H) ≤ c) (ht : 0 ≤ t) :
    (euclideanGaussianLaw H).real {z | c+t < ‖A z‖} ≤ Real.exp (-t^2/2) := by
  have hl : LipschitzWith 1 (fun z => ‖A z‖) := by
    simpa only [one_mul] using lipschitzWith_one_norm.comp (contraction_lipschitz H A hA)
  simpa only [NNReal.coe_one,one_pow,mul_one] using gaussian_upper_tail_of_mean_le H hl hc ht

theorem gaussian_leastExpansion_tail (A : H →L[ℝ] (E →L[ℝ] F)) (hA : ‖A‖ ≤ 1)
    {c t : ℝ} (hc : c ≤ ∫ z, leastExpansion (A z) ∂euclideanGaussianLaw H) (ht : 0 ≤ t) :
    (euclideanGaussianLaw H).real {z | leastExpansion (A z) < c-t} ≤ Real.exp (-t^2/2) := by
  have hl : LipschitzWith 1 (fun z => leastExpansion (A z)) := by
    simpa only [one_mul] using leastExpansion_lipschitz.comp (contraction_lipschitz H A hA)
  simpa only [NNReal.coe_one,one_pow,mul_one] using gaussian_lower_tail_of_le_mean H hl hc ht

end GradientHessian.GaussianConcentration
