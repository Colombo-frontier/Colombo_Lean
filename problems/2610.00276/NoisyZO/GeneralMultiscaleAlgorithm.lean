import NoisyZO.GeneralMultiscaleEstimator
import NoisyZO.ProjectedSGDExpectation
import NoisyZO.UnitBallProjection
import NoisyZO.RateArithmetic
import NoisyZO.QueryBudget

/-!
# General finite-smoothness multiscale algorithm

This module propagates the concrete multiscale spherical estimator through the
projected stochastic-gradient recursion.  For every fixed smoothness order
`beta > 2`, it constructs the state laws, randomized output law, and a
raw-query-budget wrapper.  The final saturated estimate has the manuscript
scaling

`min 1 ((d^2 / T)^((beta - 1) / beta))`,

with a constant depending only on the fixed smoothness order.
-/

open MeasureTheory
open scoped BigOperators Gradient InnerProductSpace NNReal ENNReal

namespace NoisyZO

noncomputable section

abbrev FullMultiscaleSample (o : SmoothnessOrder) (d : ℕ) :=
  (Fin ((o.k - 1) + 1) → ℝ × ℝ) × Point d

theorem NormalizedObjective.fullMultiscaleGaussian_projected_step
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (x : Point d)
    (xnext : FullMultiscaleSample o d → Point d)
    (η : ℝ) {h : ℝ} (hη : 0 ≤ η) (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1)
    (hnext : Integrable (fun z ↦ ‖xnext z - F.minimizer‖ ^ 2)
      (fullMultiscaleSampleMeasure d (o.k - 1) hd))
    (hprojection : ∀ z,
      ‖xnext z - F.minimizer‖ ≤
        ‖(x - η • fullMultiscaleSphericalEstimator
          d F.f (o.k - 1) x h z) - F.minimizer‖) :
    (∫ z, ‖xnext z - F.minimizer‖ ^ 2
      ∂fullMultiscaleSampleMeasure d (o.k - 1) hd) ≤
        (1 - η / 2) * ‖x - F.minimizer‖ ^ 2 -
          2 * η * (F.f x - F.f F.minimizer) +
          2 * η * (generalMultiscaleBiasConstant o * h ^ (o.beta - 1)) ^ 2 +
          η ^ 2 *
            (generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2) := by
  let μ : Measure (FullMultiscaleSample o d) :=
    fullMultiscaleSampleMeasure d (o.k - 1) hd
  let g : FullMultiscaleSample o d → Point d :=
    fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h
  have hg : Integrable g μ := by
    simpa only [g, μ] using fullMultiscaleSphericalEstimator_integrable
      hd F.f F.smooth.continuous (o.k - 1) x h
  have hgsq : Integrable (fun z ↦ ‖g z‖ ^ 2) μ := by
    simpa only [g, μ] using
      F.fullMultiscaleSphericalEstimator_sq_integrable hd x hh hh1 hx
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
  have hbias : ‖(∫ z, g z ∂μ) - ∇ F.f x‖ ≤
      generalMultiscaleBiasConstant o * h ^ (o.beta - 1) := by
    simpa only [g, μ] using
      F.norm_integral_fullMultiscaleSphericalEstimator_sub_gradient_le
        hd x hh hh1 hx
  have hmoment : (∫ z, ‖g z‖ ^ 2 ∂μ) ≤
      generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2 := by
    simpa only [g, μ] using
      F.integral_norm_fullMultiscaleSphericalEstimator_sq_le hd x hh hh1 hx
  change (∫ z, ‖xnext z - F.minimizer‖ ^ 2 ∂μ) ≤ _
  exact projected_biased_gradient_step_expectation
    μ x F.minimizer (∇ F.f x) xnext g η
    (F.f x - F.f F.minimizer)
    (generalMultiscaleBiasConstant o * h ^ (o.beta - 1))
    (generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2)
    hη hg hgsq (by simpa only [μ] using hnext)
    (by simpa only [g] using hprojection) hstrong hbias hmoment

theorem NormalizedObjective.fullMultiscaleGaussian_law_step
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (η : ℝ) {h : ℝ} (hη : 0 ≤ η) (hh : 0 < h) (hh1 : h ≤ 1)
    (xnext : Point d → FullMultiscaleSample o d → Point d)
    (hnextContinuous : Continuous (fun p : Point d × FullMultiscaleSample o d ↦
      xnext p.1 p.2))
    (hnextBall : ∀ x z, ‖xnext x z‖ ≤ 1)
    (hprojection : ∀ x z,
      ‖xnext x z - F.minimizer‖ ≤
        ‖(x - η • fullMultiscaleSphericalEstimator
          d F.f (o.k - 1) x h z) - F.minimizer‖)
    (hstate : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) :
    (∫ p, ‖xnext p.1 p.2 - F.minimizer‖ ^ 2
      ∂μ.prod (fullMultiscaleSampleMeasure d (o.k - 1) hd)) ≤
      (1 - η / 2) * (∫ x, ‖x - F.minimizer‖ ^ 2 ∂μ) -
        2 * η * (∫ x, F.f x - F.f F.minimizer ∂μ) +
        2 * η * (generalMultiscaleBiasConstant o * h ^ (o.beta - 1)) ^ 2 +
        η ^ 2 *
          (generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2) := by
  let ν : Measure (FullMultiscaleSample o d) :=
    fullMultiscaleSampleMeasure d (o.k - 1) hd
  let qfun : Point d × FullMultiscaleSample o d → ℝ :=
    fun p ↦ ‖xnext p.1 p.2 - F.minimizer‖ ^ 2
  let rfun : Point d → ℝ := fun x ↦ ‖x - F.minimizer‖ ^ 2
  let gapfun : Point d → ℝ := fun x ↦ F.f x - F.f F.minimizer
  let B : ℝ := generalMultiscaleBiasConstant o * h ^ (o.beta - 1)
  let M : ℝ := generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2
  let rhs : Point d → ℝ := fun x ↦
    (1 - η / 2) * rfun x - 2 * η * gapfun x +
      2 * η * B ^ 2 + η ^ 2 * M
  have hqMeas : AEStronglyMeasurable qfun (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [qfun]
    exact (hnextContinuous.sub continuous_const).norm.pow 2
  have hqInt : Integrable qfun (μ.prod ν) := by
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
      (integrable_const (2 * η * B ^ 2))).add
      (integrable_const (η ^ 2 * M))
  have hpoint : ∀ᵐ x ∂μ, (∫ z, qfun (x, z) ∂ν) ≤ rhs x := by
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
    have hstep := F.fullMultiscaleGaussian_projected_step hd x (xnext x)
      η hη hh hh1 hx hsliceInt (hprojection x)
    simpa only [qfun, rhs, rfun, gapfun, B, M, ν] using hstep
  have hiterated :
      (∫ x, ∫ z, qfun (x, z) ∂ν ∂μ) ≤ ∫ x, rhs x ∂μ :=
    integral_mono_ae hqInt.integral_prod_left hrhsInt hpoint
  calc
    (∫ p, ‖xnext p.1 p.2 - F.minimizer‖ ^ 2
      ∂μ.prod (fullMultiscaleSampleMeasure d (o.k - 1) hd)) =
        ∫ p, qfun p ∂μ.prod ν := by rfl
    _ = ∫ x, ∫ z, qfun (x, z) ∂ν ∂μ := integral_prod qfun hqInt
    _ ≤ ∫ x, rhs x ∂μ := hiterated
    _ = (1 - η / 2) * (∫ x, ‖x - F.minimizer‖ ^ 2 ∂μ) -
        2 * η * (∫ x, F.f x - F.f F.minimizer ∂μ) +
        2 * η * (generalMultiscaleBiasConstant o * h ^ (o.beta - 1)) ^ 2 +
        η ^ 2 *
          (generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2) := by
      change (∫ x,
        (((1 - η / 2) * rfun x - 2 * η * gapfun x) +
          2 * η * B ^ 2) + η ^ 2 * M ∂μ) = _
      have hsub : Integrable
          (fun x ↦ (1 - η / 2) * rfun x - 2 * η * gapfun x) μ :=
        (hrInt.const_mul (1 - η / 2)).sub (hgapInt.const_mul (2 * η))
      have hsubadd : Integrable
          (fun x ↦ ((1 - η / 2) * rfun x - 2 * η * gapfun x) +
            2 * η * B ^ 2) μ := hsub.add (integrable_const _)
      rw [integral_add hsubadd (integrable_const (η ^ 2 * M)),
        integral_add hsub (integrable_const (2 * η * B ^ 2)),
        integral_sub (hrInt.const_mul (1 - η / 2))
          (hgapInt.const_mul (2 * η)),
        integral_const_mul, integral_const_mul, integral_const, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl

def fullMultiscaleStateLaw {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d) :
    ℕ → Measure (Point d)
  | 0 => Measure.dirac 0
  | t + 1 =>
      ((fullMultiscaleStateLaw hd xnext t).prod
        (fullMultiscaleSampleMeasure d (o.k - 1) hd)).map
          (fun p ↦ xnext t p.1 p.2)

theorem fullMultiscaleStateLaw_isProbability
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d) (t : ℕ) :
    IsProbabilityMeasure (fullMultiscaleStateLaw hd xnext t) := by
  induction t with
  | zero =>
      simp only [fullMultiscaleStateLaw]
      infer_instance
  | succ t ih =>
      let _ : IsProbabilityMeasure (fullMultiscaleStateLaw hd xnext t) := ih
      simp only [fullMultiscaleStateLaw]
      infer_instance

theorem fullMultiscaleStateLaw_mem_unitBall
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (hnextContinuous : ∀ t,
      Continuous (fun p : Point d × FullMultiscaleSample o d ↦
        xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1) (t : ℕ) :
    ∀ᵐ x ∂fullMultiscaleStateLaw hd xnext t, ‖x‖ ≤ 1 := by
  cases t with
  | zero => simp [fullMultiscaleStateLaw]
  | succ t =>
      have hp : MeasurableSet {x : Point d | ‖x‖ ≤ 1} :=
        measurableSet_Iic.preimage continuous_norm.measurable
      rw [fullMultiscaleStateLaw,
        ae_map_iff (hnextContinuous t).measurable.aemeasurable hp]
      exact Filter.Eventually.of_forall fun p ↦ hnextBall t p.1 p.2

def fullMultiscaleLawDistance
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (t : ℕ) : ℝ :=
  ∫ x, ‖x - F.minimizer‖ ^ 2 ∂fullMultiscaleStateLaw hd xnext t

def fullMultiscaleLawGap
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (t : ℕ) : ℝ :=
  ∫ x, F.f x - F.f F.minimizer ∂fullMultiscaleStateLaw hd xnext t

set_option maxHeartbeats 800000 in
theorem NormalizedObjective.fullMultiscaleStateLaw_recurrence
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (hnextContinuous : ∀ t,
      Continuous (fun p : Point d × FullMultiscaleSample o d ↦
        xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    {h : ℝ}
    (hprojection : ∀ t x z,
      ‖xnext t x z - F.minimizer‖ ≤
        ‖(x - (4 / (t + 2 : ℝ)) • fullMultiscaleSphericalEstimator
          d F.f (o.k - 1) x h z) - F.minimizer‖)
    (hh : 0 < h) (hh1 : h ≤ 1) (t : ℕ) :
    fullMultiscaleLawDistance F hd xnext (t + 1) ≤
      (1 - (4 / (t + 2 : ℝ)) / 2) *
          fullMultiscaleLawDistance F hd xnext t -
        2 * (4 / (t + 2 : ℝ)) * fullMultiscaleLawGap F hd xnext t +
        2 * (4 / (t + 2 : ℝ)) *
          (generalMultiscaleBiasConstant o * h ^ (o.beta - 1)) ^ 2 +
        (4 / (t + 2 : ℝ)) ^ 2 *
          (generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2) := by
  let μ : Measure (Point d) := fullMultiscaleStateLaw hd xnext t
  let _ : IsProbabilityMeasure μ :=
    fullMultiscaleStateLaw_isProbability hd xnext t
  have hstep := F.fullMultiscaleGaussian_law_step hd μ
    (4 / (t + 2 : ℝ)) (by positivity) hh hh1 (xnext t)
    (hnextContinuous t) (hnextBall t) (hprojection t)
    (fullMultiscaleStateLaw_mem_unitBall hd xnext
      hnextContinuous hnextBall t)
  have hmap :
      (∫ x, ‖x - F.minimizer‖ ^ 2
        ∂fullMultiscaleStateLaw hd xnext (t + 1)) =
      ∫ p, ‖xnext t p.1 p.2 - F.minimizer‖ ^ 2
        ∂μ.prod (fullMultiscaleSampleMeasure d (o.k - 1) hd) := by
    rw [fullMultiscaleStateLaw]
    exact integral_map (hnextContinuous t).measurable.aemeasurable (by fun_prop)
  rw [fullMultiscaleLawDistance, hmap]
  simpa only [fullMultiscaleLawDistance, fullMultiscaleLawGap, μ] using hstep

def fullMultiscaleWeightedLawGap
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (n : ℕ) : ℝ :=
  2 / ((n : ℝ) * (n + 1)) *
    ∑ k ∈ Finset.range n,
      (k + 1 : ℝ) * fullMultiscaleLawGap F hd xnext k

theorem NormalizedObjective.fullMultiscaleStateLaw_weighted_gap_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (n : ℕ) (hn : 0 < n)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (hnextContinuous : ∀ t,
      Continuous (fun p : Point d × FullMultiscaleSample o d ↦
        xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    {h : ℝ}
    (hprojection : ∀ t x z,
      ‖xnext t x z - F.minimizer‖ ≤
        ‖(x - (4 / (t + 2 : ℝ)) • fullMultiscaleSphericalEstimator
          d F.f (o.k - 1) x h z) - F.minimizer‖)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    fullMultiscaleWeightedLawGap F hd xnext n ≤
      (generalMultiscaleBiasConstant o * h ^ (o.beta - 1)) ^ 2 +
        4 * (generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2) /
          (n + 1 : ℝ) := by
  let R : ℕ → ℝ := fun t ↦ fullMultiscaleLawDistance F hd xnext (t - 1)
  let Δ : ℕ → ℝ := fun t ↦ fullMultiscaleLawGap F hd xnext (t - 1)
  let B : ℝ := generalMultiscaleBiasConstant o * h ^ (o.beta - 1)
  let M : ℝ := generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 / h ^ 2
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact div_nonneg
      (mul_nonneg (generalMultiscaleMomentConstant_nonneg o)
        (sq_nonneg (d : ℝ)))
      (sq_nonneg h)
  have hR : ∀ t, 0 ≤ R t := by
    intro t
    dsimp only [R, fullMultiscaleLawDistance]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hstep : ∀ k < n,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) * Δ (k + 1) +
          2 * (4 / (k + 2 : ℝ)) * B ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 * M := by
    intro k _hk
    have hrec := F.fullMultiscaleStateLaw_recurrence hd xnext
      hnextContinuous hnextBall hprojection hh hh1 k
    have hkidx : k + 2 - 1 = k + 1 := by omega
    simpa only [R, Δ, B, M, hkidx, Nat.add_sub_cancel] using hrec
  apply biased_sgd_final_bound_of_expected_steps n hn R Δ B M
    (fullMultiscaleWeightedLawGap F hd xnext n) hM hR hstep
  dsimp only [fullMultiscaleWeightedLawGap, Δ]
  rfl

def fullMultiscaleBandwidth (o : SmoothnessOrder) (d n : ℕ) : ℝ :=
  ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ ((1 : ℝ) / (2 * o.beta))

def generalMultiscaleRateConstant (o : SmoothnessOrder) : ℝ :=
  generalMultiscaleBiasConstant o ^ 2 +
    4 * generalMultiscaleMomentConstant o

theorem generalMultiscaleRateConstant_nonneg (o : SmoothnessOrder) :
    0 ≤ generalMultiscaleRateConstant o := by
  unfold generalMultiscaleRateConstant
  exact add_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (generalMultiscaleMomentConstant_nonneg o))

theorem NormalizedObjective.fullMultiscaleStateLaw_balanced_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (n : ℕ) (hn : 0 < n) (hbudget : d ^ 2 ≤ n + 1)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (hnextContinuous : ∀ t,
      Continuous (fun p : Point d × FullMultiscaleSample o d ↦
        xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    (hprojection : ∀ t x z,
      ‖xnext t x z - F.minimizer‖ ≤
        ‖(x - (4 / (t + 2 : ℝ)) • fullMultiscaleSphericalEstimator
          d F.f (o.k - 1) x (fullMultiscaleBandwidth o d n) z) - F.minimizer‖) :
    fullMultiscaleWeightedLawGap F hd xnext n ≤
      generalMultiscaleRateConstant o *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ rateExponent o.beta := by
  let ratio : ℝ := (d : ℝ) ^ 2 / (n + 1 : ℝ)
  have hratio : 0 < ratio := by dsimp [ratio]; positivity
  have hratioOne : ratio ≤ 1 := by
    have hbudgetR : (d : ℝ) ^ 2 ≤ n + 1 := by exact_mod_cast hbudget
    dsimp only [ratio]
    exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).2 hbudgetR
  have hbeta : 0 < o.beta := lt_trans (by norm_num) o.beta_gt_two
  have hh : 0 < fullMultiscaleBandwidth o d n := by
    dsimp only [fullMultiscaleBandwidth]
    positivity
  have hh1 : fullMultiscaleBandwidth o d n ≤ 1 := by
    dsimp only [fullMultiscaleBandwidth]
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow hratio.le hratioOne (by positivity : (0 : ℝ) ≤ 1 / (2 * o.beta))
  have hmain := F.fullMultiscaleStateLaw_weighted_gap_le hd n hn xnext
    hnextContinuous hnextBall hprojection hh hh1
  calc
    fullMultiscaleWeightedLawGap F hd xnext n ≤
        (generalMultiscaleBiasConstant o *
          (fullMultiscaleBandwidth o d n) ^ (o.beta - 1)) ^ 2 +
        4 * (generalMultiscaleMomentConstant o * (d : ℝ) ^ 2 /
          (fullMultiscaleBandwidth o d n) ^ 2) / (n + 1 : ℝ) := hmain
    _ = generalMultiscaleBiasConstant o ^ 2 *
          (ratio ^ ((1 : ℝ) / (2 * o.beta))) ^ (2 * o.beta - 2) +
        4 * generalMultiscaleMomentConstant o * ratio /
          (ratio ^ ((1 : ℝ) / (2 * o.beta))) ^ (2 : ℕ) := by
      dsimp only [ratio, fullMultiscaleBandwidth]
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      have hpow :
          ((ratio ^ ((1 : ℝ) / (2 * o.beta))) ^ (o.beta - 1)) ^ 2 =
            (ratio ^ ((1 : ℝ) / (2 * o.beta))) ^ (2 * o.beta - 2) := by
        rw [← Real.rpow_two]
        rw [← Real.rpow_mul (Real.rpow_nonneg hratio.le _)]
        ring_nf
      rw [mul_pow, hpow]
      field_simp [hn1]
      ring
    _ = generalMultiscaleRateConstant o * ratio ^ rateExponent o.beta := by
      exact balanced_tradeoff hratio hbeta
    _ = generalMultiscaleRateConstant o *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ rateExponent o.beta := by rfl

def fullMultiscaleProjectedTransition
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) (x : Point d) (z : FullMultiscaleSample o d) : Point d :=
  unitBallProjection
    (x - (4 / (t + 2 : ℝ)) •
      fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z)

theorem continuous_fullMultiscaleProjectedTransition
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) :
    Continuous (fun p : Point d × FullMultiscaleSample o d ↦
      fullMultiscaleProjectedTransition F h t p.1 p.2) := by
  unfold fullMultiscaleProjectedTransition fullMultiscaleSphericalEstimator
    fullMultiscaleSphericalSignal fullMultiscaleSphericalNoise
    centralDifferenceSignal gaussianPairDifference
  apply continuous_unitBallProjection.comp
  have hfc : Continuous F.f := F.smooth.continuous
  fun_prop

theorem norm_fullMultiscaleProjectedTransition_le_one
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) (x : Point d) (z : FullMultiscaleSample o d) :
    ‖fullMultiscaleProjectedTransition F h t x z‖ ≤ 1 :=
  norm_unitBallProjection_le_one _

theorem NormalizedObjective.fullMultiscaleProjectedTransition_sub_minimizer_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) (h : ℝ)
    (t : ℕ) (x : Point d) (z : FullMultiscaleSample o d) :
    ‖fullMultiscaleProjectedTransition F h t x z - F.minimizer‖ ≤
      ‖(x - (4 / (t + 2 : ℝ)) •
        fullMultiscaleSphericalEstimator d F.f (o.k - 1) x h z) -
          F.minimizer‖ := by
  exact norm_unitBallProjection_sub_le _ _ F.minimizer_mem

theorem NormalizedObjective.fullMultiscaleProjectedStateLaw_balanced_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (n : ℕ) (hn : 0 < n) (hbudget : d ^ 2 ≤ n + 1) :
    fullMultiscaleWeightedLawGap F hd
        (fullMultiscaleProjectedTransition F (fullMultiscaleBandwidth o d n)) n ≤
      generalMultiscaleRateConstant o *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ rateExponent o.beta := by
  apply F.fullMultiscaleStateLaw_balanced_rate hd n hn hbudget
    (fullMultiscaleProjectedTransition F (fullMultiscaleBandwidth o d n))
  · exact fun t ↦ continuous_fullMultiscaleProjectedTransition F _ t
  · exact fun t x z ↦ norm_fullMultiscaleProjectedTransition_le_one F _ t x z
  · exact fun t x z ↦
      F.fullMultiscaleProjectedTransition_sub_minimizer_le _ t x z

def fullMultiscaleOutputWeight (n k : ℕ) : ℝ≥0 :=
  ⟨2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1)), by positivity⟩

@[simp]
theorem fullMultiscaleOutputWeight_coe (n k : ℕ) :
    (fullMultiscaleOutputWeight n k : ℝ) =
      2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1)) := rfl

private lemma sum_range_succ_cast_fullMultiscale (n : ℕ) :
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) =
      (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem fullMultiscaleOutputWeight_sum_one (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range n, fullMultiscaleOutputWeight n k = 1 := by
  apply NNReal.eq
  push_cast
  simp only [fullMultiscaleOutputWeight_coe]
  calc
    ∑ k ∈ Finset.range n,
        2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1)) =
        (2 / ((n : ℝ) * (n + 1))) *
          ∑ k ∈ Finset.range n, (k + 1 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = 1 := by
      rw [sum_range_succ_cast_fullMultiscale]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn0, hn1]

def fullMultiscaleOutputLaw
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (n : ℕ) : Measure (Point d) :=
  ∑ k ∈ Finset.range n,
    fullMultiscaleOutputWeight n k • fullMultiscaleStateLaw hd xnext k

theorem fullMultiscaleOutputLaw_isProbability
    {o : SmoothnessOrder} {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (fullMultiscaleOutputLaw hd xnext n) := by
  refine ⟨?_⟩
  rw [fullMultiscaleOutputLaw]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  change ∑ k ∈ Finset.range n,
      (fullMultiscaleOutputWeight n k : ℝ≥0∞) *
        (fullMultiscaleStateLaw hd xnext k) Set.univ = 1
  have huniv : ∀ k, (fullMultiscaleStateLaw hd xnext k) Set.univ = 1 := by
    intro k
    let _ : IsProbabilityMeasure (fullMultiscaleStateLaw hd xnext k) :=
      fullMultiscaleStateLaw_isProbability hd xnext k
    exact measure_univ
  have hweights := congrArg (fun q : ℝ≥0 ↦ (q : ℝ≥0∞))
    (fullMultiscaleOutputWeight_sum_one n hn)
  calc
    ∑ k ∈ Finset.range n,
        (fullMultiscaleOutputWeight n k : ℝ≥0∞) *
          (fullMultiscaleStateLaw hd xnext k) Set.univ =
        ∑ k ∈ Finset.range n,
          (fullMultiscaleOutputWeight n k : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [huniv k, mul_one]
    _ = 1 := by simpa using hweights

theorem NormalizedObjective.fullMultiscaleStateLaw_gap_integrable
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (hnextContinuous : ∀ t,
      Continuous (fun p : Point d × FullMultiscaleSample o d ↦
        xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1) (t : ℕ) :
    Integrable (fun x ↦ F.f x - F.f F.minimizer)
      (fullMultiscaleStateLaw hd xnext t) := by
  let _ : IsProbabilityMeasure (fullMultiscaleStateLaw hd xnext t) :=
    fullMultiscaleStateLaw_isProbability hd xnext t
  have hmeas : AEStronglyMeasurable (fun x ↦ F.f x - F.f F.minimizer)
      (fullMultiscaleStateLaw hd xnext t) :=
    (F.smooth.continuous.sub continuous_const).aestronglyMeasurable
  apply (integrable_const (18 : ℝ)).mono' hmeas
  filter_upwards [fullMultiscaleStateLaw_mem_unitBall hd xnext
    hnextContinuous hnextBall t] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (F.gap_nonneg x)]
  exact F.gap_le_eighteen_of_norm_le hx

theorem NormalizedObjective.integral_gap_fullMultiscaleOutputLaw
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FullMultiscaleSample o d → Point d)
    (hnextContinuous : ∀ t,
      Continuous (fun p : Point d × FullMultiscaleSample o d ↦
        xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1) (n : ℕ) :
    (∫ x, F.f x - F.f F.minimizer ∂fullMultiscaleOutputLaw hd xnext n) =
      fullMultiscaleWeightedLawGap F hd xnext n := by
  rw [fullMultiscaleOutputLaw]
  have hInt : ∀ k ∈ Finset.range n,
      Integrable (fun x ↦ F.f x - F.f F.minimizer)
        (fullMultiscaleOutputWeight n k • fullMultiscaleStateLaw hd xnext k) := by
    intro k _hk
    exact (F.fullMultiscaleStateLaw_gap_integrable hd xnext
      hnextContinuous hnextBall k).smul_measure (by simp)
  rw [integral_finsetSum_measure hInt]
  simp only [integral_smul_nnreal_measure]
  unfold fullMultiscaleWeightedLawGap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  change
    (2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1))) *
        fullMultiscaleLawGap F hd xnext k =
      (2 / ((n : ℝ) * (n + 1))) *
        ((k + 1 : ℝ) * fullMultiscaleLawGap F hd xnext k)
  ring

theorem NormalizedObjective.fullMultiscaleProjectedOutputLaw_balanced_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (n : ℕ) (hn : 0 < n) (hbudget : d ^ 2 ≤ n + 1) :
    (∫ x, F.f x - F.f F.minimizer
      ∂fullMultiscaleOutputLaw hd
        (fullMultiscaleProjectedTransition F (fullMultiscaleBandwidth o d n)) n) ≤
      generalMultiscaleRateConstant o *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ rateExponent o.beta := by
  rw [F.integral_gap_fullMultiscaleOutputLaw hd
    (fullMultiscaleProjectedTransition F (fullMultiscaleBandwidth o d n))
    (fun t ↦ continuous_fullMultiscaleProjectedTransition F _ t)
    (fun t x z ↦ norm_fullMultiscaleProjectedTransition_le_one F _ t x z) n]
  exact F.fullMultiscaleProjectedStateLaw_balanced_rate hd n hn hbudget

def fullMultiscaleRawCalls (o : SmoothnessOrder) : ℕ :=
  2 * ((o.k - 1) + 1)

theorem fullMultiscaleRawCalls_pos (o : SmoothnessOrder) :
    0 < fullMultiscaleRawCalls o := by
  unfold fullMultiscaleRawCalls
  have hk := o.two_le_k
  omega

def fullMultiscaleHighBudgetRateConstant (o : SmoothnessOrder) : ℝ :=
  generalMultiscaleRateConstant o *
    (2 * (fullMultiscaleRawCalls o : ℝ)) ^ rateExponent o.beta

def fullMultiscaleRawRateConstant (o : SmoothnessOrder) : ℝ :=
  (generalMultiscaleRateConstant o + 9) *
    (2 * (fullMultiscaleRawCalls o : ℝ)) ^ rateExponent o.beta

theorem fullMultiscaleRawRateConstant_nonneg (o : SmoothnessOrder) :
    0 ≤ fullMultiscaleRawRateConstant o := by
  unfold fullMultiscaleRawRateConstant
  apply mul_nonneg
  · linarith [generalMultiscaleRateConstant_nonneg o]
  · exact Real.rpow_nonneg (by positivity) _

theorem NormalizedObjective.fullMultiscaleProjectedOutputLaw_raw_budget_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (T : ℕ)
    (hlarge : 2 * fullMultiscaleRawCalls o * d ^ 2 ≤ T) :
    (∫ x, F.f x - F.f F.minimizer
      ∂fullMultiscaleOutputLaw hd
        (fullMultiscaleProjectedTransition F
          (fullMultiscaleBandwidth o d (T / fullMultiscaleRawCalls o)))
        (T / fullMultiscaleRawCalls o)) ≤
      fullMultiscaleHighBudgetRateConstant o *
        ((d : ℝ) ^ 2 / T) ^ rateExponent o.beta := by
  let q : ℕ := fullMultiscaleRawCalls o
  let n : ℕ := T / q
  have hq : 0 < q := fullMultiscaleRawCalls_pos o
  have hd2 : 0 < d ^ 2 := pow_pos hd _
  have hdOne : 1 ≤ d ^ 2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd2)
  have hqle : q ≤ T := by
    have hqTwo : q ≤ 2 * q := by omega
    have htwoLe : 2 * q ≤ 2 * q * d ^ 2 := by
      have hmul := Nat.mul_le_mul_left (2 * q) hdOne
      simpa using hmul
    exact (hqTwo.trans htwoLe).trans (by simpa only [q] using hlarge)
  have hn : 0 < n := by
    simpa only [n] using Nat.div_pos hqle hq
  have hbudget : d ^ 2 ≤ n + 1 := by
    have hqbudget : q * d ^ 2 ≤ T := by
      calc
        q * d ^ 2 ≤ (2 * q) * d ^ 2 :=
          Nat.mul_le_mul_right (d ^ 2) (by omega)
        _ ≤ T := by simpa only [q] using hlarge
    have hdiv : d ^ 2 ≤ T / q :=
      (Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hqbudget)
    omega
  have hmain := F.fullMultiscaleProjectedOutputLaw_balanced_rate
    hd n hn hbudget
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1R : 0 < (n + 1 : ℝ) := by positivity
  have hTtwo : 2 * q ≤ T := by
    have hdOne : 1 ≤ d ^ 2 := by omega
    nlinarith
  have hratioSucc :
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ (d : ℝ) ^ 2 / n := by
    apply (div_le_div_iff₀ hn1R hnR).2
    nlinarith [sq_nonneg (d : ℝ)]
  have hscheduled :
      (d : ℝ) ^ 2 / n ≤ 2 * q * (d : ℝ) ^ 2 / T := by
    simpa only [n] using dimension_ratio_scheduled_le (d := d) (T := T)
      (q := q) hq hTtwo
  have hratio :
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤
        (2 * q : ℝ) * ((d : ℝ) ^ 2 / T) := by
    calc
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ (d : ℝ) ^ 2 / n := hratioSucc
      _ ≤ 2 * q * (d : ℝ) ^ 2 / T := hscheduled
      _ = (2 * q : ℝ) * ((d : ℝ) ^ 2 / T) := by ring
  have hbetaPos : 0 < o.beta := lt_trans (by norm_num) o.beta_gt_two
  have hnumPos : 0 < o.beta - 1 := by linarith [o.beta_gt_two]
  have hpPos : 0 < rateExponent o.beta := by
    unfold rateExponent
    exact div_pos hnumPos hbetaPos
  have hpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ (d : ℝ) ^ 2 / (n + 1 : ℝ)) hratio hpPos.le
  calc
    (∫ x, F.f x - F.f F.minimizer
      ∂fullMultiscaleOutputLaw hd
        (fullMultiscaleProjectedTransition F
          (fullMultiscaleBandwidth o d (T / fullMultiscaleRawCalls o)))
        (T / fullMultiscaleRawCalls o)) ≤
        generalMultiscaleRateConstant o *
          ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ rateExponent o.beta := by
      simpa only [n, q] using hmain
    _ ≤ generalMultiscaleRateConstant o *
        ((2 * q : ℝ) * ((d : ℝ) ^ 2 / T)) ^ rateExponent o.beta := by
      exact mul_le_mul_of_nonneg_left hpow
        (generalMultiscaleRateConstant_nonneg o)
    _ = fullMultiscaleHighBudgetRateConstant o *
        ((d : ℝ) ^ 2 / T) ^ rateExponent o.beta := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      unfold fullMultiscaleHighBudgetRateConstant
      dsimp only [q]
      ring

def fullMultiscaleProjectedBudgetOutputLaw
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (T : ℕ) : Measure (Point d) :=
  if 2 * fullMultiscaleRawCalls o * d ^ 2 ≤ T then
    fullMultiscaleOutputLaw hd
      (fullMultiscaleProjectedTransition F
        (fullMultiscaleBandwidth o d (T / fullMultiscaleRawCalls o)))
      (T / fullMultiscaleRawCalls o)
  else Measure.dirac 0

theorem fullMultiscaleProjectedBudgetOutputLaw_isProbability
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (T : ℕ) (hT : 0 < T) :
    IsProbabilityMeasure (fullMultiscaleProjectedBudgetOutputLaw F hd T) := by
  unfold fullMultiscaleProjectedBudgetOutputLaw
  split_ifs with hlarge
  · apply fullMultiscaleOutputLaw_isProbability
    have hq := fullMultiscaleRawCalls_pos o
    have hd2 : 0 < d ^ 2 := pow_pos hd _
    have hdOne : 1 ≤ d ^ 2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd2)
    have hqle : fullMultiscaleRawCalls o ≤ T := by
      have hqTwo : fullMultiscaleRawCalls o ≤
          2 * fullMultiscaleRawCalls o := by omega
      have htwoLe : 2 * fullMultiscaleRawCalls o ≤
          2 * fullMultiscaleRawCalls o * d ^ 2 := by
        have hmul := Nat.mul_le_mul_left (2 * fullMultiscaleRawCalls o) hdOne
        simpa using hmul
      exact (hqTwo.trans htwoLe).trans hlarge
    exact Nat.div_pos hqle hq
  · infer_instance

theorem NormalizedObjective.fullMultiscaleProjectedBudgetOutputLaw_saturated_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (T : ℕ) (hT : 0 < T) :
    (∫ x, F.f x - F.f F.minimizer
      ∂fullMultiscaleProjectedBudgetOutputLaw F hd T) ≤
      fullMultiscaleRawRateConstant o *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent o.beta) := by
  let q : ℕ := fullMultiscaleRawCalls o
  have hq : 0 < q := fullMultiscaleRawCalls_pos o
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hbetaPos : 0 < o.beta := lt_trans (by norm_num) o.beta_gt_two
  have hnumPos : 0 < o.beta - 1 := by linarith [o.beta_gt_two]
  have hp : 0 < rateExponent o.beta := by
    unfold rateExponent
    exact div_pos hnumPos hbetaPos
  by_cases hlarge : 2 * q * d ^ 2 ≤ T
  · have hmain := F.fullMultiscaleProjectedOutputLaw_raw_budget_rate
      hd T (by simpa only [q] using hlarge)
    have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
    have hratioOne : (d : ℝ) ^ 2 / T ≤ 1 := by
      rw [div_le_one hTR]
      have hd2leNat : d ^ 2 ≤ T := by
        have hqOne : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
        have htwoqOne : 1 ≤ 2 * q := by omega
        have hle : d ^ 2 ≤ (2 * q) * d ^ 2 := by
          have hmul := Nat.mul_le_mul_right (d ^ 2) htwoqOne
          simpa using hmul
        exact hle.trans hlarge
      exact_mod_cast hd2leNat
    have hpowOne :
        ((d : ℝ) ^ 2 / T) ^ rateExponent o.beta ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by positivity : 0 ≤ (d : ℝ) ^ 2 / T)
          hratioOne hp.le
    rw [fullMultiscaleProjectedBudgetOutputLaw, if_pos (by simpa only [q] using hlarge),
      min_eq_right hpowOne]
    calc
      (∫ x, F.f x - F.f F.minimizer
        ∂fullMultiscaleOutputLaw hd
          (fullMultiscaleProjectedTransition F
            (fullMultiscaleBandwidth o d (T / fullMultiscaleRawCalls o)))
          (T / fullMultiscaleRawCalls o)) ≤
          fullMultiscaleHighBudgetRateConstant o *
            ((d : ℝ) ^ 2 / T) ^ rateExponent o.beta := hmain
      _ ≤ fullMultiscaleRawRateConstant o *
          ((d : ℝ) ^ 2 / T) ^ rateExponent o.beta := by
        have hbaseNonneg : 0 ≤
            (2 * (fullMultiscaleRawCalls o : ℝ)) ^ rateExponent o.beta :=
          Real.rpow_nonneg (by positivity) _
        have hconst : fullMultiscaleHighBudgetRateConstant o ≤
            fullMultiscaleRawRateConstant o := by
          unfold fullMultiscaleHighBudgetRateConstant
            fullMultiscaleRawRateConstant
          exact mul_le_mul_of_nonneg_right
            (by linarith [generalMultiscaleRateConstant_nonneg o]) hbaseNonneg
        exact mul_le_mul_of_nonneg_right hconst
          (Real.rpow_nonneg
            (div_nonneg (sq_nonneg (d : ℝ)) hTR.le) _)
  · have hsmall : T < 2 * q * d ^ 2 := Nat.lt_of_not_ge hlarge
    have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
    have hsmallR : (T : ℝ) < 2 * q * (d : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hfloorPos : 0 < (1 / (2 * q : ℝ)) := by positivity
    have hratioLower : (1 / (2 * q : ℝ)) < (d : ℝ) ^ 2 / T := by
      rw [lt_div_iff₀ hTR]
      calc
        (1 / (2 * q : ℝ)) * T = T / (2 * q : ℝ) := by ring
        _ < (d : ℝ) ^ 2 :=
          (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2 (by
            nlinarith [hsmallR])
    have hpowLower :
        (1 / (2 * q : ℝ)) ^ rateExponent o.beta ≤
          ((d : ℝ) ^ 2 / T) ^ rateExponent o.beta :=
      Real.rpow_le_rpow hfloorPos.le hratioLower.le hp.le
    have hfloorOne : (1 / (2 * q : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2 * q)]
      have htwoqNat : 1 ≤ 2 * q := by omega
      exact_mod_cast htwoqNat
    have hpowFloor :
        (1 / (2 * q : ℝ)) ^ rateExponent o.beta ≤
          min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent o.beta) := by
      apply le_min
      · simpa only [Real.one_rpow] using
          Real.rpow_le_rpow hfloorPos.le hfloorOne hp.le
      · exact hpowLower
    have hcancel :
        (2 * (q : ℝ)) ^ rateExponent o.beta *
          (1 / (2 * q : ℝ)) ^ rateExponent o.beta = 1 := by
      rw [← Real.mul_rpow (by positivity) hfloorPos.le]
      have hbase : (2 * (q : ℝ)) * (1 / (2 * q : ℝ)) = 1 := by
        field_simp [ne_of_gt hqR]
      rw [hbase, Real.one_rpow]
    rw [fullMultiscaleProjectedBudgetOutputLaw,
      if_neg (by simpa only [q] using hlarge), integral_dirac]
    calc
      F.f 0 - F.f F.minimizer ≤ 9 := F.zero_gap_le_nine
      _ ≤ generalMultiscaleRateConstant o + 9 := by
        linarith [generalMultiscaleRateConstant_nonneg o]
      _ = (generalMultiscaleRateConstant o + 9) *
          (2 * (q : ℝ)) ^ rateExponent o.beta *
            (1 / (2 * q : ℝ)) ^ rateExponent o.beta := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ (generalMultiscaleRateConstant o + 9) *
          (2 * (q : ℝ)) ^ rateExponent o.beta *
            min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent o.beta) := by
        exact mul_le_mul_of_nonneg_left hpowFloor
          (mul_nonneg
            (by linarith [generalMultiscaleRateConstant_nonneg o])
            (Real.rpow_nonneg (by positivity) _))
      _ = fullMultiscaleRawRateConstant o *
          min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent o.beta) := by
        unfold fullMultiscaleRawRateConstant
        dsimp only [q]

end

end NoisyZO
