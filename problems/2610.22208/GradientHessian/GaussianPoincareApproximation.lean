import GradientHessian.GaussianPoincareSmooth
import Mathlib.Probability.Variance

/-! Poincare passes to smooth approximation. Every approximating estimate
is proved from Gaussian calculus; the premises specify only convergence
of the first moment, second moment, and actual derivative energy. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Filter
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_poincare_of_smooth_approximation {f : E → ℝ} {energy : ℝ}
    (hf : MemLp f 2 (euclideanGaussianLaw E))
    (F : ℕ → E → ℝ) (B C : ℕ → ℝ≥0) (D : ℕ → ℝ)
    (hF : ∀ n, ContDiff ℝ 2 (F n)) (hLip : ∀ n, LipschitzWith (B n) (F n))
    (hH : ∀ n x, ‖fderiv ℝ (fderiv ℝ (F n)) x‖ ≤ (C n : ℝ))
    (hD : ∀ n x, ‖F n x‖ ≤ D n)
    (hmean : Tendsto (fun n => ∫ x, F n x ∂euclideanGaussianLaw E) atTop
      (𝓝 (∫ x, f x ∂euclideanGaussianLaw E)))
    (hsecond : Tendsto (fun n => ∫ x, F n x ^ 2 ∂euclideanGaussianLaw E) atTop
      (𝓝 (∫ x, f x ^ 2 ∂euclideanGaussianLaw E)))
    (henergy : Tendsto (fun n => ∫ x, ‖fderiv ℝ (F n) x‖ ^ 2 ∂euclideanGaussianLaw E)
      atTop (𝓝 energy)) :
    variance f (euclideanGaussianLaw E) ≤ energy := by
  rw [variance_def' hf]
  exact le_of_tendsto_of_tendsto (hsecond.sub (hmean.pow 2)) henergy
    (Eventually.of_forall fun n => gaussian_poincare_bounded_smooth E
      (hF n) (hLip n) (hH n) (hD n))

end GradientHessian.GaussianConcentration
