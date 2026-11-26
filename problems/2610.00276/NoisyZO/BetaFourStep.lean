import NoisyZO.GaussianFourNoise
import NoisyZO.ProjectedSGDExpectation

/-!
# Concrete projected step for the four-query estimator

This module inserts the explicit uniform-sphere/four-Gaussian estimator into
the expected projected-SGD inequality, including the proved surface-to-ball
smoothing identity.
-/

open MeasureTheory
open scoped Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

/-- One projected stochastic-gradient step driven by the concrete `β = 4`
four-query estimator.  All integrability, Gaussian moments, bias, and
second-moment premises are discharged internally. -/
theorem NormalizedObjective.betaFourGaussian_projected_step
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (x : Point d) (xnext :
      Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d)
    (η : ℝ) {h : ℝ} (hη : 0 ≤ η) (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1)
    (hnext : Integrable (fun z ↦ ‖xnext z - F.minimizer‖ ^ 2)
      ((uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure))
    (hprojection : ∀ z,
      ‖xnext z - F.minimizer‖ ≤
        ‖(x - η • betaFourSphericalEstimator d F.f x h z.1
          z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) - F.minimizer‖) :
    (∫ z, ‖xnext z - F.minimizer‖ ^ 2
      ∂(uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure) ≤
        (1 - η / 2) * ‖x - F.minimizer‖ ^ 2 -
          2 * η * (F.f x - F.f F.minimizer) +
          2 * η * (h ^ 3 / 12) ^ 2 +
          η ^ 2 * (229 * d ^ 2 / h ^ 2) := by
  let μ : Measure (Point d × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure
  let g : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalEstimator d F.f x h z.1
      z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
  have hg : Integrable g μ := by
    simpa only [g, μ] using
      F.betaFourGaussianEstimator_integrable hd x hh hh1 hx
  have hgsq : Integrable (fun z ↦ ‖g z‖ ^ 2) μ := by
    simpa only [g, μ] using
      F.betaFourGaussianEstimator_sq_integrable hd x hh hh1 hx
  have hstrong :
      (F.f x - F.f F.minimizer) +
          (1 / 2 : ℝ) * ‖x - F.minimizer‖ ^ 2 ≤
        ⟪∇ F.f x, x - F.minimizer⟫_ℝ := by
    have hs := F.strong x F.minimizer
    have hinner :
        ⟪∇ F.f x, F.minimizer - x⟫_ℝ =
          -⟪∇ F.f x, x - F.minimizer⟫_ℝ := by
      rw [show F.minimizer - x = -(x - F.minimizer) by abel,
        inner_neg_right]
    rw [hinner, norm_sub_rev F.minimizer x] at hs
    linarith
  have hbias : ‖(∫ z, g z ∂μ) - ∇ F.f x‖ ≤ h ^ 3 / 12 := by
    simpa only [g, μ] using
      F.norm_integral_betaFourGaussianEstimator_sub_gradient_le
        hbeta hd x hh hh1 hx
  have hmoment : (∫ z, ‖g z‖ ^ 2 ∂μ) ≤
      229 * d ^ 2 / h ^ 2 := by
    simpa only [g, μ] using
      F.integral_norm_betaFourGaussianEstimator_sq_le hd x hh hh1 hx
  change (∫ z, ‖xnext z - F.minimizer‖ ^ 2 ∂μ) ≤ _
  exact projected_biased_gradient_step_expectation
    μ x F.minimizer (∇ F.f x) xnext g η
    (F.f x - F.f F.minimizer) (h ^ 3 / 12)
    (229 * d ^ 2 / h ^ 2)
    hη hg hgsq (by simpa only [μ] using hnext)
    (by simpa only [g] using hprojection) hstrong hbias hmoment

end

end NoisyZO
