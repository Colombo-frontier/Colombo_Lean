import GradientHessian.GaussianEntropyDissipation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Sharp Gaussian log-Sobolev inequality on bounded positive C2 inputs,
proved from actual entropy dissipation and Fisher-information contraction. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter Set
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_logSobolev_bounded_smooth {g : E → ℝ} {B C : ℝ≥0} {a b : ℝ}
    (hg : ContDiff ℝ 2 g) (hLip : LipschitzWith B g)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ (C : ℝ))
    (ha : 0 < a) (hab : ∀ x, a ≤ g x ∧ g x ≤ b) :
    (∫ x, g x * Real.log (g x) ∂euclideanGaussianLaw E) -
        (∫ x, g x ∂euclideanGaussianLaw E) * Real.log (∫ x, g x ∂euclideanGaussianLaw E) ≤
      (1 / 2 : ℝ) * ∫ x, ‖fderiv ℝ g x‖ ^ 2 / g x ∂euclideanGaussianLaw E := by
  let A := ∫ x, fisherIntegrand E g x ∂euclideanGaussianLaw E
  let F : ℝ → ℝ := fun t =>
    (∫ x, ornsteinUhlenbeck E t g x * Real.log (ornsteinUhlenbeck E t g x)
      ∂euclideanGaussianLaw E) - Real.exp (-t) ^ 2 * A / 2
  let F' : ℝ → ℝ := fun t =>
    -(∫ x, fisherIntegrand E (ornsteinUhlenbeck E t g) x ∂euclideanGaussianLaw E) +
      Real.exp (-t) ^ 2 * A
  have hD (x : E) : ‖g x‖ ≤ b := by
    rw [Real.norm_of_nonneg (ha.trans_le (hab x).1).le]
    exact (hab x).2
  have hc : Continuous F :=
    (ouFunctional_continuous E hg.continuous hD Real.continuous_mul_log).sub
      ((((Real.continuous_exp.comp continuous_neg).pow 2).mul continuous_const).div_const 2)
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt F (F' t) t := by
    convert (ou_entropy_hasDerivAt E hg hLip hH ha hab ht).sub
      ((((ou_signal_hasDerivAt t).pow 2).mul_const A).div_const 2) using 1
    dsimp [F, F']
    ring
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc.continuousOn
      (fun t ht => (hd t (by simpa only [interior_Ici, mem_Ioi] using ht)).hasDerivWithinAt)
    intro t ht
    have ht' : 0 ≤ t := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using ht)
    have he := ou_fisher_contraction E hg hLip hH ha hab ht'
    dsimp [F', A]
    linarith
  have hl : Tendsto F atTop
      (𝓝 ((∫ x, g x ∂euclideanGaussianLaw E) * Real.log (∫ x, g x ∂euclideanGaussianLaw E))) := by
    have hz : Tendsto (fun t : ℝ => Real.exp (-t) ^ 2 * A / 2) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).mul_const A).div_const 2
    simpa only [sub_zero] using
      (ouFunctional_tendsto E hg.continuous hD Real.continuous_mul_log).sub hz
  have hle : F 0 ≤
      (∫ x, g x ∂euclideanGaussianLaw E) * Real.log (∫ x, g x ∂euclideanGaussianLaw E) := by
    apply ge_of_tendsto hl
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with t ht
    exact hm (by simp) ht ht
  have he : F 0 = (∫ x, g x * Real.log (g x) ∂euclideanGaussianLaw E) - A / 2 := by
    simp [F, ornsteinUhlenbeck]
  rw [he] at hle
  dsimp [A, fisherIntegrand] at hle
  linarith

end GradientHessian.GaussianConcentration
