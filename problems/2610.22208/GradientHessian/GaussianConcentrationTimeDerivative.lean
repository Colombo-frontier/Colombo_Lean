import GradientHessian.GaussianConcentrationDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Differentiation in time of the actual Ornstein--Uhlenbeck Gaussian
integral, justified by a local integrable bound of constant-plus-linear growth. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Filter
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem affine_gaussian_hasDerivAt {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith B f)
    {a a' b b' : ℝ → ℝ} {t : ℝ}
    (ha : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s)
    (hb : ∀ᶠ s in 𝓝 t, HasDerivAt b (b' s) s)
    (ha' : ContinuousAt a' t) (hb' : ContinuousAt b' t) (x : E) :
    HasDerivAt (fun s => ∫ z, f (a s • x + b s • z) ∂euclideanGaussianLaw E)
      (∫ z, fderiv ℝ f (a t • x + b t • z) (a' t • x + b' t • z)
        ∂euclideanGaussianLaw E) t := by
  have hea : ∀ᶠ s in 𝓝 t, ‖a' s‖ < ‖a' t‖ + 1 :=
    ha'.norm.eventually (gt_mem_nhds (by linarith : ‖a' t‖ < ‖a' t‖ + 1))
  have heb : ∀ᶠ s in 𝓝 t, ‖b' s‖ < ‖b' t‖ + 1 :=
    hb'.norm.eventually (gt_mem_nhds (by linarith : ‖b' t‖ < ‖b' t‖ + 1))
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp (ha.and (hb.and (hea.and heb)))
  let F : ℝ → E → ℝ := fun s z => f (a s • x + b s • z)
  let F' : ℝ → E → ℝ := fun s z =>
    fderiv ℝ f (a s • x + b s • z) (a' s • x + b' s • z)
  let bound : E → ℝ := fun z => (B : ℝ) * ((‖a' t‖ + 1) * ‖x‖ + (‖b' t‖ + 1) * ‖z‖)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (euclideanGaussianLaw E) := by
    apply Eventually.of_forall
    intro s
    exact (hf.continuous.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  have h'int : Integrable (F t) (euclideanGaussianLaw E) :=
    lipschitz_affine_integrable hLip (b t) (a t • x)
  have h'dmeas : AEStronglyMeasurable (F' t) (euclideanGaussianLaw E) := by
    apply Continuous.aestronglyMeasurable
    exact ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_const.smul continuous_id))).clm_apply
      (continuous_const.add (continuous_const.smul continuous_id))
  have hbnd : ∀ᵐ z ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε, ‖F' s z‖ ≤ bound z := by
    apply ae_of_all
    intro z s hs
    have hls := hlocal s hs
    have hv : ‖a' s • x + b' s • z‖ ≤ (‖a' t‖ + 1) * ‖x‖ + (‖b' t‖ + 1) * ‖z‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_smul, norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right hls.2.2.1.le (norm_nonneg x))
        (mul_le_mul_of_nonneg_right hls.2.2.2.le (norm_nonneg z))
    calc
      ‖F' s z‖ ≤ ‖fderiv ℝ f (a s • x + b s • z)‖ * ‖a' s • x + b' s • z‖ :=
        (fderiv ℝ f _).le_opNorm _
      _ ≤ (B : ℝ) * ((‖a' t‖ + 1) * ‖x‖ + (‖b' t‖ + 1) * ‖z‖) :=
        mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hLip) hv (norm_nonneg _) B.coe_nonneg
  have hbound : Integrable bound (euclideanGaussianLaw E) :=
    ((integrable_const _).add ((norm_integrable E).const_mul (‖b' t‖ + 1))).const_mul (B : ℝ)
  have hdiff : ∀ᵐ z ∂euclideanGaussianLaw E, ∀ s ∈ Metric.ball t ε,
      HasDerivAt (fun r => F r z) (F' s z) s := by
    apply ae_of_all
    intro z s hs
    have hls := hlocal s hs
    exact (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s
      ((hls.1.smul_const x).add (hls.2.1.smul_const z))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas h'int h'dmeas hbnd hbound hdiff).2

theorem ou_signal_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  simpa only [mul_neg_one] using (hasDerivAt_id t).neg.exp

theorem ou_noise_positive {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) ^ 2 := by
  have h : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  nlinarith [Real.exp_pos (-t)]

theorem ou_noise_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-s) ^ 2))
      (Real.exp (-t) ^ 2 / Real.sqrt (1 - Real.exp (-t) ^ 2)) t := by
  convert (((ou_signal_hasDerivAt t).pow 2).const_sub 1).sqrt (ou_noise_positive ht).ne' using 1
  ring

theorem ornsteinUhlenbeck_time_hasDerivAt {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith B f) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => ornsteinUhlenbeck E s f x)
      (∫ z, fderiv ℝ f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • z)
        ((-Real.exp (-t)) • x +
          (Real.exp (-t) ^ 2 / Real.sqrt (1 - Real.exp (-t) ^ 2)) • z)
        ∂euclideanGaussianLaw E) t := by
  apply affine_gaussian_hasDerivAt hf hLip (Eventually.of_forall ou_signal_hasDerivAt)
  · filter_upwards [eventually_gt_nhds ht] with s hs
    exact ou_noise_hasDerivAt hs
  · fun_prop
  · exact ((Real.continuous_exp.comp continuous_neg).continuousAt.pow 2).div
      ((Real.continuous_sqrt.comp (continuous_const.sub ((Real.continuous_exp.comp continuous_neg).pow 2))).continuousAt)
      (Real.sqrt_pos.2 (ou_noise_positive ht)).ne'

end GradientHessian.GaussianConcentration
