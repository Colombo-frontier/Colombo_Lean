import HaarRebalancingRootMoment
import SphereConcentrationHalfMass

/-!
The actual Markov-to-root cutoff step for the spherical third-halves moment.
-/

open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.SphereConcentration
open scoped ENNReal NNReal

namespace Task006.HaarRebalancing
noncomputable section

/-- Apply Markov to the actual third-halves power and invert the monotone
power map. No median or half-mass sublevel is assumed. -/
theorem lower_half_of_threeHalves_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {a : Ω → ℝ} {M : ℝ}
    (hnonneg : ∀ ω, 0 ≤ a ω)
    (hint : Integrable (fun ω => a ω ^ (3 / 2 : ℝ)) μ)
    (hM : 0 < M) (hmean : (∫ ω, a ω ^ (3 / 2 : ℝ) ∂μ) ≤ M) :
    (1 / 2 : ℝ) ≤ μ.real {ω | a ω ≤ (2 * M) ^ (2 / 3 : ℝ)} := by
  have hhalf := lower_half_of_integral_bound hint
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hnonneg ω) _)) hM hmean
  have hsubset : {ω | a ω ^ (3 / 2 : ℝ) ≤ 2 * M} ⊆
      {ω | a ω ≤ (2 * M) ^ (2 / 3 : ℝ)} := by
    intro ω hω
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg (hnonneg ω) _) hω
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← Real.rpow_mul (hnonneg ω)] at hp
    norm_num at hp
    exact hp
  exact hhalf.trans (measureReal_mono hsubset)

end
end Task006.HaarRebalancing
