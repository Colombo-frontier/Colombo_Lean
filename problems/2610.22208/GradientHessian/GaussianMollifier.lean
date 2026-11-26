import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual convolution with a normalized compact smooth bump preserves
the Lipschitz constant and approximates the input quantitatively. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ContinuousLinearMap Metric
open scoped Convolution NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def mollify (φ : ContDiffBump (0 : E)) (μ : Measure E) (f : E → ℝ) : E → ℝ :=
  φ.normed μ ⋆[lsmul ℝ ℝ, μ] f

theorem mollify_lipschitz (φ : ContDiffBump (0 : E)) {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) : LipschitzWith B (mollify φ μ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : Integrable (fun z => φ.normed μ z * f (x - z)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable hLip.continuous x
  have hy : Integrable (fun z => φ.normed μ z * f (y - z)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable hLip.continuous y
  change ‖(∫ z, φ.normed μ z * f (x - z) ∂μ) -
    (∫ z, φ.normed μ z * f (y - z) ∂μ)‖ ≤ (B : ℝ) * dist x y
  rw [← integral_sub hx hy]
  have hb : ∀ z, ‖φ.normed μ z * f (x - z) - φ.normed μ z * f (y - z)‖ ≤
      φ.normed μ z * ((B : ℝ) * dist x y) := by
    intro z
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed z)]
    have h := hLip.dist_le_mul (x - z) (y - z)
    rw [dist_sub_right, dist_eq_norm] at h
    exact mul_le_mul_of_nonneg_left h (φ.nonneg_normed z)
  calc
    _ ≤ ∫ z, ‖φ.normed μ z * f (x - z) - φ.normed μ z * f (y - z)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ.normed μ z * ((B : ℝ) * dist x y) ∂μ :=
      integral_mono (hx.sub hy).norm (φ.integrable_normed.mul_const _) hb
    _ = _ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem mollify_smooth (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) : ContDiff ℝ 2 (mollify φ μ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf.locallyIntegrable

theorem mollify_compact (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hs : HasCompactSupport f) : HasCompactSupport (mollify φ μ f) :=
  φ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hs

theorem mollify_error (φ : ContDiffBump (0 : E)) {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) (x : E) :
    dist (mollify φ μ f x) (f x) ≤ (B : ℝ) * φ.rOut := by
  apply φ.dist_normed_convolution_le hLip.continuous.aestronglyMeasurable
  intro y hy
  exact (hLip.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le B.coe_nonneg)

end GradientHessian.GaussianConcentration
