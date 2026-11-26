import NoisyZO.BetaFourStep
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating a concrete estimator step over a random current state

This is the measure-level replacement for informal conditioning on the SGD
history.  Fubini integrates the already-proved fresh-noise step over an
arbitrary probability law of the current iterate.
-/

open MeasureTheory
open scoped Gradient InnerProductSpace

namespace NoisyZO

noncomputable section

abbrev FourQuerySample (d : ℕ) := Point d × ((ℝ × ℝ) × (ℝ × ℝ))

/-- A concrete fresh-noise projected step can be averaged over any random
current iterate supported in the unit ball.  This derives the unconditional
SGD recurrence without taking conditional expectation as a primitive. -/
theorem NormalizedObjective.betaFourGaussian_law_step
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (η : ℝ) {h : ℝ} (hη : 0 ≤ η) (hh : 0 < h) (hh1 : h ≤ 1)
    (xnext : Point d → FourQuerySample d → Point d)
    (hnextContinuous : Continuous (fun p : Point d × FourQuerySample d ↦
      xnext p.1 p.2))
    (hnextBall : ∀ x z, ‖xnext x z‖ ≤ 1)
    (hprojection : ∀ x z,
      ‖xnext x z - F.minimizer‖ ≤
        ‖(x - η • betaFourSphericalEstimator d F.f x h z.1
          z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) - F.minimizer‖)
    (hstate : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) :
    (∫ p, ‖xnext p.1 p.2 - F.minimizer‖ ^ 2
      ∂μ.prod ((uniformUnitSphere d hd : Measure (Point d)).prod
        fourNoiseMeasure)) ≤
      (1 - η / 2) * (∫ x, ‖x - F.minimizer‖ ^ 2 ∂μ) -
        2 * η * (∫ x, F.f x - F.f F.minimizer ∂μ) +
        2 * η * (h ^ 3 / 12) ^ 2 +
        η ^ 2 * (229 * d ^ 2 / h ^ 2) := by
  let ν : Measure (FourQuerySample d) :=
    (uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure
  let q : Point d × FourQuerySample d → ℝ :=
    fun p ↦ ‖xnext p.1 p.2 - F.minimizer‖ ^ 2
  let rfun : Point d → ℝ := fun x ↦ ‖x - F.minimizer‖ ^ 2
  let gapfun : Point d → ℝ := fun x ↦ F.f x - F.f F.minimizer
  let rhs : Point d → ℝ := fun x ↦
    (1 - η / 2) * rfun x - 2 * η * gapfun x +
      2 * η * (h ^ 3 / 12) ^ 2 +
      η ^ 2 * (229 * d ^ 2 / h ^ 2)
  have hqMeas : AEStronglyMeasurable q (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [q]
    exact (hnextContinuous.sub continuous_const).norm.pow 2
  have hqInt : Integrable q (μ.prod ν) := by
    apply (integrable_const (4 : ℝ)).mono' hqMeas
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hdist : ‖xnext p.1 p.2 - F.minimizer‖ ≤ 2 := by
      calc
        ‖xnext p.1 p.2 - F.minimizer‖ ≤
            ‖xnext p.1 p.2‖ + ‖F.minimizer‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith [hnextBall p.1 p.2, F.minimizer_mem]
    nlinarith [norm_nonneg (xnext p.1 p.2 - F.minimizer)]
  have hrMeas : AEStronglyMeasurable rfun μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [rfun]
    fun_prop
  have hrInt : Integrable rfun μ := by
    apply (integrable_const (4 : ℝ)).mono' hrMeas
    filter_upwards [hstate] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hdist : ‖x - F.minimizer‖ ≤ 2 := by
      calc
        ‖x - F.minimizer‖ ≤ ‖x‖ + ‖F.minimizer‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith [F.minimizer_mem]
    nlinarith [norm_nonneg (x - F.minimizer)]
  have hgapMeas : AEStronglyMeasurable gapfun μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [gapfun]
    exact F.smooth.continuous.sub continuous_const
  have hgapInt : Integrable gapfun μ := by
    apply (integrable_const (18 : ℝ)).mono' hgapMeas
    filter_upwards [hstate] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (F.gap_nonneg x)]
    exact F.gap_le_eighteen_of_norm_le hx
  have hrhsInt : Integrable rhs μ := by
    exact (((hrInt.const_mul (1 - η / 2)).sub
      (hgapInt.const_mul (2 * η))).add
      (integrable_const (2 * η * (h ^ 3 / 12) ^ 2))).add
      (integrable_const (η ^ 2 * (229 * (d : ℝ) ^ 2 / h ^ 2)))
  have hpoint : ∀ᵐ x ∂μ,
      (∫ z, q (x, z) ∂ν) ≤ rhs x := by
    filter_upwards [hstate] with x hx
    have hsliceContinuous : Continuous (xnext x) :=
      hnextContinuous.comp (continuous_const.prodMk continuous_id)
    have hsliceInt : Integrable
        (fun z ↦ ‖xnext x z - F.minimizer‖ ^ 2) ν := by
      apply (integrable_const (4 : ℝ)).mono'
        ((hsliceContinuous.sub continuous_const).norm.pow 2).aestronglyMeasurable
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change ‖xnext x z - F.minimizer‖ ^ 2 ≤ 4
      have hdist : ‖xnext x z - F.minimizer‖ ≤ 2 := by
        calc
          ‖xnext x z - F.minimizer‖ ≤
              ‖xnext x z‖ + ‖F.minimizer‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith [hnextBall x z, F.minimizer_mem]
      nlinarith [norm_nonneg (xnext x z - F.minimizer)]
    have hstep := F.betaFourGaussian_projected_step hbeta hd x (xnext x)
      η hη hh hh1 hx hsliceInt (hprojection x)
    simpa only [q, rhs, rfun, gapfun, ν] using hstep
  have hiterated :
      (∫ x, ∫ z, q (x, z) ∂ν ∂μ) ≤ ∫ x, rhs x ∂μ := by
    exact integral_mono_ae hqInt.integral_prod_left hrhsInt hpoint
  calc
    (∫ p, ‖xnext p.1 p.2 - F.minimizer‖ ^ 2
      ∂μ.prod ((uniformUnitSphere d hd : Measure (Point d)).prod
        fourNoiseMeasure)) = ∫ p, q p ∂μ.prod ν := by rfl
    _ = ∫ x, ∫ z, q (x, z) ∂ν ∂μ := integral_prod q hqInt
    _ ≤ ∫ x, rhs x ∂μ := hiterated
    _ = (1 - η / 2) * (∫ x, ‖x - F.minimizer‖ ^ 2 ∂μ) -
        2 * η * (∫ x, F.f x - F.f F.minimizer ∂μ) +
        2 * η * (h ^ 3 / 12) ^ 2 +
        η ^ 2 * (229 * d ^ 2 / h ^ 2) := by
      change (∫ x,
        (((1 - η / 2) * rfun x - 2 * η * gapfun x) +
          2 * η * (h ^ 3 / 12) ^ 2) +
          η ^ 2 * (229 * (d : ℝ) ^ 2 / h ^ 2) ∂μ) = _
      have hsub : Integrable
          (fun x ↦ (1 - η / 2) * rfun x - 2 * η * gapfun x) μ :=
        (hrInt.const_mul (1 - η / 2)).sub (hgapInt.const_mul (2 * η))
      have hsubadd : Integrable
          (fun x ↦ ((1 - η / 2) * rfun x - 2 * η * gapfun x) +
            2 * η * (h ^ 3 / 12) ^ 2) μ :=
        hsub.add (integrable_const _)
      rw [integral_add
          hsubadd
          (integrable_const (η ^ 2 * (229 * (d : ℝ) ^ 2 / h ^ 2))),
        integral_add
          hsub
          (integrable_const (2 * η * (h ^ 3 / 12) ^ 2)),
        integral_sub (hrInt.const_mul (1 - η / 2))
          (hgapInt.const_mul (2 * η)),
        integral_const_mul, integral_const_mul, integral_const, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl

end

end NoisyZO
