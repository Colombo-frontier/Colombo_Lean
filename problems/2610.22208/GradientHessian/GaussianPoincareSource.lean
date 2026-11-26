import GradientHessian.GaussianPoincareL2
import GradientHessian.GaussianBumpCutoff

/-! Source-form Poincare for a gradient defined by compact smooth L2
approximation. No derivative bounds of the approximants are premises;
they follow from their actual compact support. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Filter
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem compact_c2_memLp {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    MemLp f 2 (euclideanGaussianLaw E) := by
  obtain ⟨D, hD⟩ := hs.exists_bound_of_continuous hf.continuous
  exact bounded_smooth_memLp E hf hD

theorem compact_c2_gradient_memLp {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    MemLp (gradient f) 2 (euclideanGaussianLaw E) := by
  obtain ⟨B, hB⟩ := compact_smooth_lipschitz_exists (hf.of_le (by norm_num)) hs
  exact smooth_gradient_memLp E hf hB

structure GaussianGradientApproximation (f : E → ℝ) (G : E → E) where
  function_memLp : MemLp f 2 (euclideanGaussianLaw E)
  gradient_memLp : MemLp G 2 (euclideanGaussianLaw E)
  approximants : ℕ → E → ℝ
  smooth : ∀ n, ContDiff ℝ 2 (approximants n)
  compact : ∀ n, HasCompactSupport (approximants n)
  function_limit : Tendsto
    (fun n => (compact_c2_memLp E (smooth n) (compact n)).toLp (approximants n))
    atTop (𝓝 (function_memLp.toLp f))
  gradient_limit : Tendsto
    (fun n => (compact_c2_gradient_memLp E (smooth n) (compact n)).toLp (gradient (approximants n)))
    atTop (𝓝 (gradient_memLp.toLp G))

theorem gaussian_poincare {f : E → ℝ} {G : E → E}
    (h : GaussianGradientApproximation E f G) :
    variance f (euclideanGaussianLaw E) ≤ ∫ x, ‖G x‖ ^ 2 ∂euclideanGaussianLaw E := by
  have hbounds (n : ℕ) : ∃ B C : ℝ≥0, ∃ D : ℝ,
      LipschitzWith B (h.approximants n) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (h.approximants n)) x‖ ≤ (C : ℝ)) ∧
      (∀ x, ‖h.approximants n x‖ ≤ D) := by
    obtain ⟨B, hB⟩ := compact_smooth_lipschitz_exists ((h.smooth n).of_le (by norm_num)) (h.compact n)
    obtain ⟨D, hD⟩ := (h.compact n).exists_bound_of_continuous (h.smooth n).continuous
    have hc : Continuous (fderiv ℝ (fderiv ℝ (h.approximants n))) :=
      ((h.smooth n).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
    obtain ⟨C, hC⟩ := (((h.compact n).fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hc
    exact ⟨B, ⟨C, (norm_nonneg _).trans (hC 0)⟩, D, hB, hC, hD⟩
  choose B C D hB hC hD using hbounds
  exact gaussian_poincare_of_L2_approximation E h.function_memLp h.gradient_memLp
    h.approximants B C D h.smooth hB hC hD h.function_limit h.gradient_limit

end GradientHessian.GaussianConcentration
