import GradientHessian.GaussianPoincareDissipation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Sharp Gaussian Poincare for bounded C2 functions with bounded first
and second derivatives. This is deduced from the actual semigroup. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter Set
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_poincare_bounded_smooth {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) :
    (∫ x, (f x) ^ 2 ∂euclideanGaussianLaw E) -
        (∫ x, f x ∂euclideanGaussianLaw E) ^ 2 ≤
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂euclideanGaussianLaw E := by
  let A := ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂euclideanGaussianLaw E
  let F : ℝ → ℝ := fun t =>
    (∫ x, (ornsteinUhlenbeck E t f x) ^ 2 ∂euclideanGaussianLaw E) - Real.exp (-t) ^ 2 * A
  let F' : ℝ → ℝ := fun t =>
    -2 * (∫ x, ‖fderiv ℝ (ornsteinUhlenbeck E t f) x‖ ^ 2 ∂euclideanGaussianLaw E) +
      2 * Real.exp (-t) ^ 2 * A
  have hc : Continuous F :=
    (ou_squareMean_continuous E hf.continuous hD).sub
      (((Real.continuous_exp.comp continuous_neg).pow 2).mul continuous_const)
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt F (F' t) t := by
    convert (ou_squareMean_hasDerivAt E hf hLip hH hD ht).sub
      (((ou_signal_hasDerivAt t).pow 2).mul_const A) using 1
    dsimp [F, F']
    ring
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc.continuousOn
      (fun t ht => (hd t (by simpa only [interior_Ici, mem_Ioi] using ht)).hasDerivWithinAt)
    intro t ht
    have ht' : 0 ≤ t := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using ht)
    have he := ou_energy_contraction E hf hLip hH ht'
    dsimp [F', A]
    linarith
  have hl : Tendsto F atTop (𝓝 ((∫ x, f x ∂euclideanGaussianLaw E) ^ 2)) := by
    have hz : Tendsto (fun t : ℝ => Real.exp (-t) ^ 2 * A) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.pow 2).mul_const A
    simpa only [sub_zero] using (ou_squareMean_tendsto E hf.continuous hD).sub hz
  have hle : F 0 ≤ (∫ x, f x ∂euclideanGaussianLaw E) ^ 2 := by
    apply ge_of_tendsto hl
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with t ht
    exact hm (by simp) ht ht
  have he : F 0 = (∫ x, (f x) ^ 2 ∂euclideanGaussianLaw E) - A := by
    simp [F, ornsteinUhlenbeck]
  rw [he] at hle
  dsimp [A] at hle
  linarith

end GradientHessian.GaussianConcentration
