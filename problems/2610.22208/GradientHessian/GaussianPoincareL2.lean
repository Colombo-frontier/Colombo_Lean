import GradientHessian.GaussianPoincareApproximation
import GradientHessian.GaussianL2Limits
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Gaussian Poincare for functions whose gradient is defined by smooth
L2 approximation. Both function and gradient convergence use actual L2
spaces; no estimate on the approximants is an assumption. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Filter
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem bounded_smooth_memLp {f : E → ℝ} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hD : ∀ x, ‖f x‖ ≤ D) :
    MemLp f 2 (euclideanGaussianLaw E) :=
  MemLp.of_bound hf.continuous.aestronglyMeasurable D (ae_of_all _ hD)

theorem smooth_gradient_memLp {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f) :
    MemLp (gradient f) 2 (euclideanGaussianLaw E) := by
  apply MemLp.of_bound
    (((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num))).aestronglyMeasurable) (B : ℝ)
  apply ae_of_all
  intro x
  simpa only [Function.comp_apply, LinearIsometryEquiv.norm_map] using
    (norm_fderiv_le_of_lipschitz ℝ hLip : ‖fderiv ℝ f x‖ ≤ (B : ℝ))

theorem gaussian_poincare_of_L2_approximation {f : E → ℝ} {G : E → E}
    (hf : MemLp f 2 (euclideanGaussianLaw E)) (hG : MemLp G 2 (euclideanGaussianLaw E))
    (F : ℕ → E → ℝ) (B C : ℕ → ℝ≥0) (D : ℕ → ℝ)
    (hF : ∀ n, ContDiff ℝ 2 (F n)) (hLip : ∀ n, LipschitzWith (B n) (F n))
    (hH : ∀ n x, ‖fderiv ℝ (fderiv ℝ (F n)) x‖ ≤ (C n : ℝ))
    (hD : ∀ n x, ‖F n x‖ ≤ D n)
    (hfunction : Tendsto
      (fun n => (bounded_smooth_memLp E (hF n) (hD n)).toLp (F n)) atTop (𝓝 (hf.toLp f)))
    (hgradient : Tendsto
      (fun n => (smooth_gradient_memLp E (hF n) (hLip n)).toLp (gradient (F n)))
      atTop (𝓝 (hG.toLp G))) :
    variance f (euclideanGaussianLaw E) ≤ ∫ x, ‖G x‖ ^ 2 ∂euclideanGaussianLaw E := by
  have hmean := integral_tendsto_of_L2
    (fun n => bounded_smooth_memLp E (hF n) (hD n)) hf hfunction
  have hsecond := integral_norm_square_tendsto_of_L2
    (fun n => bounded_smooth_memLp E (hF n) (hD n)) hf hfunction
  have henergy := integral_norm_square_tendsto_of_L2
    (fun n => smooth_gradient_memLp E (hF n) (hLip n)) hG hgradient
  simp only [Real.norm_eq_abs, sq_abs] at hsecond
  simp only [gradient, LinearIsometryEquiv.norm_map] at henergy
  exact gaussian_poincare_of_smooth_approximation E hf F B C D hF hLip hH hD
    hmean hsecond henergy

end GradientHessian.GaussianConcentration
