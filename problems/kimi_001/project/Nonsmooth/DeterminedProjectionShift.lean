import Nonsmooth.ConstantObservationAE
import Nonsmooth.SupportWinnerRank

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem rankQuantileLog_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ rankQuantileLog p := by
  by_cases h0 : p = 0
  · simp [h0, rankQuantileLog]
  by_cases h1 : p = 1
  · simp [h1, rankQuantileLog]
  have hm : 0 < min p (1 - p) := lt_min (lt_of_le_of_ne hp0 (Ne.symm h0))
    (sub_pos.mpr (lt_of_le_of_ne hp1 h1))
  apply Real.log_nonneg
  exact (le_div_iff₀ hm).mpr (by nlinarith [min_le_left p (1 - p)])

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem projectionPosteriorShift_zero_of_constant (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u : E) (c : ℝ)
    (hc : ∀ᵐ z ∂μ, ⟪z, u⟫_ℝ = c) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ), projectionPosteriorShift μ u y = 0 := by
  filter_upwards [ae_constant_observation_posterior μ _ (by fun_prop) c hc] with y hy
  unfold projectionPosteriorShift
  rw [hy, integral_sub hi (integrable_const _), integral_const,
    measureReal_univ_eq_one, one_smul, sub_self]

theorem projection_rank_of_constant (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u : E) (c : ℝ)
    (hc : ∀ᵐ z ∂μ, ⟪z, u⟫_ℝ = c) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        K * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  filter_upwards [projectionPosteriorShift_zero_of_constant μ hi u c hc] with y hy
  rw [hy, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  exact mul_nonneg hK (add_nonneg zero_le_one (rankQuantileLog_nonneg (cdf_nonneg _ _) (cdf_le_one _ _)))

end
end Nonsmooth
