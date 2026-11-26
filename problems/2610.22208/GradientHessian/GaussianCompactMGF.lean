import GradientHessian.GaussianSmoothMGF

/-! Compact smooth functions require no assumed derivative estimates:
compact support itself supplies the Hessian bound for the MGF theorem. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_compact_smooth_centered_mgf {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (hLip : LipschitzWith B f) (t : ℝ) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E)) ∂euclideanGaussianLaw E) ≤
      Real.exp (t ^ 2 * (B : ℝ) ^ 2 / 2) := by
  obtain ⟨D, hD⟩ := hs.exists_bound_of_continuous hf.continuous
  have hHc : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := ((hs.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hHc
  have hCn : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  exact gaussian_smooth_centered_mgf E hf hLip (C := ⟨C, hCn⟩) hC hD t

end GradientHessian.GaussianConcentration
