import GradientHessian.GaussianConcentrationTails

/-! One-sided Gaussian concentration around any proved upper or lower
bound on the actual mean, with the strict events used for singular values. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_upper_tail_of_mean_le {f : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B f)
    {c t : ℝ} (hc : (∫ x, f x ∂euclideanGaussianLaw E) ≤ c) (ht : 0 ≤ t) :
    (euclideanGaussianLaw E).real {x | c+t < f x} ≤ Real.exp (-t^2/(2*(B:ℝ)^2)) := by
  apply le_trans (measureReal_mono (show {x | c+t < f x} ⊆
    {x | t ≤ f x - ∫ y, f y ∂euclideanGaussianLaw E} from ?_))
    (gaussian_lipschitz_right_tail E hLip ht)
  intro x hx
  change c+t < f x at hx
  change t ≤ f x - ∫ y, f y ∂euclideanGaussianLaw E
  linarith

theorem gaussian_lower_tail_of_le_mean {f : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B f)
    {c t : ℝ} (hc : c ≤ ∫ x, f x ∂euclideanGaussianLaw E) (ht : 0 ≤ t) :
    (euclideanGaussianLaw E).real {x | f x < c-t} ≤ Real.exp (-t^2/(2*(B:ℝ)^2)) := by
  have h := gaussian_lipschitz_right_tail E hLip.neg ht
  simp only [Pi.neg_apply,integral_neg] at h
  apply le_trans (measureReal_mono (show {x | f x < c-t} ⊆
    {x | t ≤ -f x - -(∫ y, f y ∂euclideanGaussianLaw E)} from ?_)) h
  intro x hx
  change f x < c-t at hx
  change t ≤ -f x - -(∫ y, f y ∂euclideanGaussianLaw E)
  linarith

end GradientHessian.GaussianConcentration
