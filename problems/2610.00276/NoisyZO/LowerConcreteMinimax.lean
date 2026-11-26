import NoisyZO.LowerAlgorithmOutput
import NoisyZO.LowerMinimaxBridge
import NoisyZO.RadialProfileUniformBounds

/-!
# Concrete adaptive algorithms and the lower minimax risk

This module packages measurable query, state-update, and returned-point maps
as an algorithm type over a fixed randomized state space.  The algorithm-level
hard-family theorem then feeds directly into `minimaxRisk`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NoisyZO

noncomputable section

/-- A finite-horizon adaptive Gaussian zeroth-order algorithm represented on
a fixed measurable randomized state space. -/
structure AdaptiveGaussianAlgorithm
    (α : Type*) [MeasurableSpace α] (d : ℕ) where
  query : ℕ → α → Point d
  query_measurable : ∀ t, Measurable (query t)
  update : ℕ → α × ℝ → α
  update_measurable : ∀ t, Measurable (update t)
  output : α → Point d
  output_measurable : Measurable output
  output_mem : ∀ z, ‖output z‖ ≤ 1

/-- The two remaining perturbation derivative certificates for the canonical
rate-scaled hard family. -/
abbrev LowerRateQuantitativeCertificates
    (o : SmoothnessOrder) (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) :=
  ∀ s : Hypercube d,
    RadialHardQuantitativeCertificate o d
      (a * lowerBandwidth a d T β ^ (β - 1))
      (lowerBandwidth a d T β)
      (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
        (lt_trans (by norm_num) hβ)) s

/-- Uniform dimension-free bounds for the unit-scale radial profiles. -/
abbrev LowerRateUnitProfileCertificates
    (o : SmoothnessOrder) (d : ℕ) (M₂ H : ℝ) :=
  ∀ s : Hypercube d, UnitRadialProfileCertificate o d s M₂ H

/-- The unit-profile estimates generate the rate-scaled perturbation
certificates at the bandwidth used in the lower bound. -/
theorem lowerRateQuantitativeCertificatesOfUnitProfile
    {o : SmoothnessOrder} {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    (a M₂ H : ℝ) (ha : 0 < a)
    (profile : LowerRateUnitProfileCertificates o d M₂ H)
    (haM₂ : a * M₂ ≤ 1) (haH : a * H ≤ 1) :
    LowerRateQuantitativeCertificates o d T hd hT o.beta a
      o.beta_gt_two ha := by
  intro s
  exact radialHardQuantitativeCertificateOfUnitProfileSmall
    s a (lowerBandwidth a d T o.beta) M₂ H ha
    (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
      (lt_trans (by norm_num) o.beta_gt_two))
    (lowerBandwidth_le_one a d T o.beta)
    (profile s) haM₂ haH

/-- Expected optimization gap of a concrete adaptive algorithm on a canonical
hard-family vertex. -/
def lowerRateAlgorithmRisk
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α)
    (cert : LowerRateQuantitativeCertificates o d T hd hT β a hβ ha)
    (A : AdaptiveGaussianAlgorithm α d) (s : Hypercube d) : ℝ :=
  ∫ x,
    (lowerRateHardObjective hd hT β a hβ ha ha4 cert s).f x -
      (lowerRateHardObjective hd hT β a hβ ha ha4 cert s).f
        (lowerRateHardObjective hd hT β a hβ ha ha4 cert s).minimizer
    ∂hardAdaptiveOutputLaw μ₀
      (a * lowerBandwidth a d T β ^ (β - 1))
      (lowerBandwidth a d T β)
      (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
        (lt_trans (by norm_num) hβ))
      A.query A.query_measurable A.update A.update_measurable T A.output s

/-- Every concrete algorithm obeys the canonical average hard-family lower rate. -/
theorem lowerRateAlgorithmRisk_average
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (cert : LowerRateQuantitativeCertificates o d T hd hT β a hβ ha)
    (A : AdaptiveGaussianAlgorithm α d) :
    (3 * a ^ 2 / 64) *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β) ≤
      (∑ s : Hypercube d,
        lowerRateAlgorithmRisk hd hT β a hβ ha ha4 μ₀ cert A s) /
          (2 : ℝ) ^ d := by
  exact hard_family_adaptive_gaussian_lower_rate_of_quantitative_certificate
    hd hT β a hβ ha ha4 μ₀
    A.query A.query_measurable A.update A.update_measurable
    A.output A.output_measurable A.output_mem cert

/-- Concrete minimax lower bound over packaged adaptive algorithms and the
canonical Boolean hard family. -/
theorem lowerRate_le_concrete_minimaxRisk
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (cert : LowerRateQuantitativeCertificates o d T hd hT β a hβ ha) :
    ENNReal.ofReal
        ((3 * a ^ 2 / 64) *
          min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β)) ≤
      minimaxRisk (fun A : AdaptiveGaussianAlgorithm α d ↦
        fun s : Hypercube d ↦
          ENNReal.ofReal
            (lowerRateAlgorithmRisk hd hT β a hβ ha ha4 μ₀ cert A s)) := by
  apply ofReal_le_minimaxRisk_of_average_hypercube
  intro A
  exact lowerRateAlgorithmRisk_average
    hd hT β a hβ ha ha4 μ₀ cert A

/-- Smoothness-order-aligned concrete minimax lower bound whose only analytic
input is the dimension-free unit-profile certificate from Appendix A. -/
theorem lowerRate_le_concrete_minimaxRisk_of_unit_profile
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (a M₂ H : ℝ) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (profile : LowerRateUnitProfileCertificates o d M₂ H)
    (haM₂ : a * M₂ ≤ 1) (haH : a * H ≤ 1) :
    ENNReal.ofReal
        ((3 * a ^ 2 / 64) *
          min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent o.beta)) ≤
      minimaxRisk (fun A : AdaptiveGaussianAlgorithm α d ↦
        fun s : Hypercube d ↦
          ENNReal.ofReal
            (lowerRateAlgorithmRisk hd hT o.beta a o.beta_gt_two ha ha4 μ₀
              (lowerRateQuantitativeCertificatesOfUnitProfile
                hd hT a M₂ H ha profile haM₂ haH) A s)) := by
  exact lowerRate_le_concrete_minimaxRisk
    hd hT o.beta a o.beta_gt_two ha ha4 μ₀
    (lowerRateQuantitativeCertificatesOfUnitProfile
      hd hT a M₂ H ha profile haM₂ haH)

/-- The quantitative hard-family certificates obtained from the fixed
dimension-free radial-profile data. -/
theorem dimensionFreeLowerRateQuantitativeCertificates
    {o : SmoothnessOrder} {d T : ℕ} (hd : 0 < d) (hT : 0 < T) :
    LowerRateQuantitativeCertificates o d T hd hT o.beta
      (dimensionFreeRadialProfileData o).amplitude o.beta_gt_two
      (dimensionFreeRadialProfileData o).amplitude_pos :=
  lowerRateQuantitativeCertificatesOfUnitProfile
    hd hT
    (dimensionFreeRadialProfileData o).amplitude
    (dimensionFreeRadialProfileData o).M₂
    (dimensionFreeRadialProfileData o).H
    (dimensionFreeRadialProfileData o).amplitude_pos
    (fun s ↦ (dimensionFreeRadialProfileData o).profile d s)
    (dimensionFreeRadialProfileData o).amplitude_mul_M₂_le_one
    (dimensionFreeRadialProfileData o).amplitude_mul_H_le_one

/-- Assumption-free concrete minimax lower bound for the explicit radial hard
family.  Its positive amplitude depends only on the smoothness order, not on
the dimension or query budget. -/
theorem lowerRate_le_concrete_minimaxRisk_dimension_free
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀] :
    ENNReal.ofReal
        ((3 * (dimensionFreeRadialProfileData o).amplitude ^ 2 / 64) *
          min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent o.beta)) ≤
      minimaxRisk (fun A : AdaptiveGaussianAlgorithm α d ↦
        fun s : Hypercube d ↦
          ENNReal.ofReal
            (lowerRateAlgorithmRisk hd hT o.beta
              (dimensionFreeRadialProfileData o).amplitude o.beta_gt_two
              (dimensionFreeRadialProfileData o).amplitude_pos
              (dimensionFreeRadialProfileData o).amplitude_le_quarter μ₀
              (dimensionFreeLowerRateQuantitativeCertificates hd hT) A s)) := by
  simpa [dimensionFreeLowerRateQuantitativeCertificates] using
    lowerRate_le_concrete_minimaxRisk_of_unit_profile
      hd hT
      (dimensionFreeRadialProfileData o).amplitude
      (dimensionFreeRadialProfileData o).M₂
      (dimensionFreeRadialProfileData o).H
      (dimensionFreeRadialProfileData o).amplitude_pos
      (dimensionFreeRadialProfileData o).amplitude_le_quarter μ₀
      (fun s ↦ (dimensionFreeRadialProfileData o).profile d s)
      (dimensionFreeRadialProfileData o).amplitude_mul_M₂_le_one
      (dimensionFreeRadialProfileData o).amplitude_mul_H_le_one

end

end NoisyZO
