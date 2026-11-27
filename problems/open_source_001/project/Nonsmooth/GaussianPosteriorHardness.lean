import Nonsmooth.GaussianOutputCriterion
import Nonsmooth.PosteriorBudget

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Quantitative estimates for the actual Gaussian conditional means and residuals.
CompleteGaussianHardness proves this proposition with constant 512. -/
def GaussianPosteriorEstimates (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] (C : ℝ) : Prop :=
  ∀ (k : ℕ) (hk : 0 < k),
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    4096 ≤ Module.finrank ℝ E → (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512 →
    ∀ (S : Type) (mS : MeasurableSpace S), letI := mS
      ∀ p : Policy Unit S E, p.IsMeasurable →
        let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
        (∀ n : ℕ, (∫ a, ‖gaussianSupportMean p () (n + 1) a - gaussianSupportMean p () n a‖ ^ 2 ∂Q) ≤
          C * Real.log (Real.exp 1 * k) / (Module.finrank ℝ E : ℝ)) ∧
        (∀ (n : ℕ) (X : (Fin k → E) → E),
          AEStronglyMeasurable[supportTranscriptInformation p () n] X Q → (∀ a, ‖X a‖ ≤ 1) →
          (∫ a, ⟪(∑ i, a i) - gaussianSupportMean p () n a, X a⟫_ℝ ^ 2 ∂Q) ≤
            (k : ℝ) / (Module.finrank ℝ E : ℝ))

theorem gaussian_adaptive_hardness_of_posterior_estimates {C : ℝ} (hC : 0 ≤ C)
    (hest : GaussianPosteriorEstimates E C) :
    GaussianAdaptiveHardnessInput E (posteriorSupportProbabilityConstant C) := by
  intro k hk hdmin hkd T hT S mS p hp
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  by_cases hd : 4096 ≤ Module.finrank ℝ E
  · have hq := supportAmbientPolicy_measurable p hp
    have hpost := hest k hk hd hkd S mS (supportAmbientPolicy p) hq
    have he := gaussian_support_energy_from_steps (k := k) (supportAmbientPolicy p) hq () T
      (fun n _ => hpost.1 n)
    have heNumeric := posterior_budget_energy_numeric Module.finrank_pos hk hC hT
    have henergy : (∫ a : Fin k → E, ‖gaussianSupportMean (supportAmbientPolicy p) () T a‖ ^ 2
        ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤ (k : ℝ) / 4096 := by
      exact (he.trans heNumeric).trans (by have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have hX : @Measurable (Fin k → E) E
        (supportTranscriptInformation (supportAmbientPolicy p) () T) inferInstance (supportPolicyOutput p () T) := by
      have h := support_output_transcript_measurable (k := k) (supportAmbientPolicy p) hq () T
      convert! h using 1
      funext a
      simp only [supportAmbientPolicy_result, supportPolicyOutput]
    have hXb (a : Fin k → E) : ‖supportPolicyOutput p () T a‖ ≤ 1 := (p.result _ () T).property
    have hr := hpost.2 T (supportPolicyOutput p () T) hX.aestronglyMeasurable hXb
    have hresidual : (∫ a : Fin k → E,
        ⟪(∑ i, a i) - gaussianSupportMean (supportAmbientPolicy p) () T a, supportPolicyOutput p () T a⟫_ℝ ^ 2
          ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤ (k : ℝ) / 4096 := by
      apply hr.trans
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by norm_num : (0 : ℝ) < 4096)
      exact_mod_cast hd
    exact gaussianSupportPrior_gap_of_posterior_moments hk p hp () T hdmin hkd henergy hresidual
  · have hzero := posterior_budget_small_dimension_zero hk hC (by omega) hkd hT
    subst T
    exact gaussianSupportPrior_zero_query_gap hdmin hk hkd p ()

theorem supportHardnessInput_of_posterior_estimates {C : ℝ} (hC : 0 ≤ C)
    (hest : GaussianPosteriorEstimates E C) :
    SupportHardnessInput E (1 / 512) (posteriorSupportProbabilityConstant C) (1 / 4) 256 :=
  supportHardnessInput_of_gaussian_adaptive (gaussian_adaptive_hardness_of_posterior_estimates hC hest)

end
end Nonsmooth
