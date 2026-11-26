import GradientHessian.GaussianCompactMGF
import GradientHessian.GaussianCutoffApproximation

/-! Sharp centered MGF bound for every Lipschitz function under the
actual standard Gaussian law. Compact smooth approximants are constructed
and both expectation limits are justified by integrable domination. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Filter
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_lipschitz_centered_mgf {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) (t : ℝ) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E)) ∂euclideanGaussianLaw E) ≤
      Real.exp (t ^ 2 * (B : ℝ) ^ 2 / 2) := by
  obtain ⟨F, hF, hS, hL, hBound, hlim⟩ := exists_compact_smooth_lipschitz_approximation hLip
  let A := (B : ℝ) + 1
  have hmean : Tendsto (fun n => ∫ x, F n x ∂euclideanGaussianLaw E) atTop
      (𝓝 (∫ x, f x ∂euclideanGaussianLaw E)) :=
    tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ + A)
      (Eventually.of_forall fun n => (hF n).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun n => ae_of_all _ (hBound n))
      ((lipschitz_integrable hLip).norm.add (integrable_const A)) (ae_of_all _ hlim)
  have hnorm : LipschitzWith B (fun x => ‖f x‖ + A) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_add_right]
    exact (dist_norm_norm_le _ _).trans (hLip.dist_le_mul x y)
  have hmgf : Tendsto (fun n => mgf (F n) (euclideanGaussianLaw E) t) atTop
      (𝓝 (mgf f (euclideanGaussianLaw E) t)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => Real.exp (|t| * (‖f x‖ + A)))
    · exact Eventually.of_forall fun n =>
        ((continuous_const.mul (hF n).continuous).rexp).aestronglyMeasurable
    · apply Eventually.of_forall
      intro n
      apply ae_of_all
      intro x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      calc
        t * F n x ≤ |t * F n x| := le_abs_self _
        _ = |t| * ‖F n x‖ := by rw [abs_mul, Real.norm_eq_abs]
        _ ≤ |t| * (‖f x‖ + A) := mul_le_mul_of_nonneg_left (hBound n x) (abs_nonneg t)
    · exact lipschitz_exponential_integrable hnorm |t|
    · exact ae_of_all _ fun x => (Real.continuous_exp.tendsto _).comp ((hlim x).const_mul t)
  have hcenter : Tendsto
      (fun n => ∫ x, Real.exp (t * (F n x - ∫ y, F n y ∂euclideanGaussianLaw E))
        ∂euclideanGaussianLaw E) atTop
      (𝓝 (∫ x, Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E))
        ∂euclideanGaussianLaw E)) := by
    simp_rw [gaussian_centered_mgf_eq]
    exact hmgf.mul ((Real.continuous_exp.tendsto _).comp (hmean.const_mul (-t)))
  have hright : Tendsto
      (fun n => Real.exp (t ^ 2 * (approximationLipschitz B n : ℝ) ^ 2 / 2)) atTop
      (𝓝 (Real.exp (t ^ 2 * (B : ℝ) ^ 2 / 2))) :=
    (Real.continuous_exp.tendsto _).comp
      ((((approximationLipschitz_tendsto B).pow 2).const_mul (t ^ 2)).div_const 2)
  exact le_of_tendsto_of_tendsto hcenter hright
    (Eventually.of_forall fun n => gaussian_compact_smooth_centered_mgf E (hF n) (hS n) (hL n) t)

end GradientHessian.GaussianConcentration
