import NoisyZO.AssouadDecision
import NoisyZO.LowerCore

/-!
# Adaptive lower rate for concrete output laws

The adaptive Gaussian lower theorem is instantiated with the coordinate
decoder applied to actual output distributions.  Its edge-testing inequality
and Hamming-to-loss premise are discharged automatically.  Only the analytic
Pinsker bound for the selected measurable events remains explicit, since that
inequality is not currently available in mathlib.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NoisyZO

noncomputable section

/-- Concrete-output-law form of the full adaptive lower rate.  Compared with
`hard_family_adaptive_gaussian_lower_rate`, the free `err`, `tv`, `hedge`,
`risk`, and `hpoint` arguments have disappeared. -/
theorem hard_family_adaptive_gaussian_lower_rate_of_output_laws
    {o : SmoothnessOrder} {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (law : Hypercube d → Measure (Point d))
    [∀ s, IsProbabilityMeasure (law s)]
    (F : Hypercube d → NormalizedObjective o d)
    (hmin : ∀ s,
      (F s).minimizer =
        signCenter
          ((a * lowerBandwidth a d T β ^ (β - 1)) /
            (2 * Real.sqrt d)) s)
    (hgap : ∀ s, Integrable
      (fun x ↦ (F s).f x - (F s).f (F s).minimizer) (law s))
    (hpinsker : ∀ s i,
      assouadEdgeEventDistance law s i ≤ Real.sqrt
        ((InformationTheory.klDiv
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query s)
            (hardGaussianMean_measurable
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query hquery s)
            update hupdate T)
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query (flipHypercube s i))
            (hardGaussianMean_measurable
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query hquery (flipHypercube s i))
            update hupdate T)).toReal / 2)) :
    (3 * a ^ 2 / 64) *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β) ≤
      (∑ s : Hypercube d,
        (∫ x, (F s).f x - (F s).f (F s).minimizer ∂law s)) /
          (2 : ℝ) ^ d := by
  have hh : 0 < lowerBandwidth a d T β :=
    lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
      (lt_trans (by norm_num) hβ)
  have hcenter :
      0 ≤ (a * lowerBandwidth a d T β ^ (β - 1)) /
        (2 * Real.sqrt d) := by
    exact div_nonneg
      (mul_nonneg ha.le (Real.rpow_nonneg hh.le _))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  apply hard_family_adaptive_gaussian_lower_rate hd hT β a hβ ha ha4
    μ₀ query hquery update hupdate
    (assouadErrorProbability law) (assouadEdgeEventDistance law)
    (fun s ↦ ∫ x, (F s).f x - (F s).f (F s).minimizer ∂law s)
  · exact fun s i ↦ assouadErrorProbability_edge law s i
  · exact hpinsker
  · intro s
    exact (F s).expected_hamming_to_gap law
      ((a * lowerBandwidth a d T β ^ (β - 1)) /
        (2 * Real.sqrt d))
      hcenter s (hmin s) (hgap s)

end

end NoisyZO
