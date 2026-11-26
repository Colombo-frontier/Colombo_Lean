import HeavyTail.GaussianStageTuning
import HeavyTail.AcceptedRateTuning

/-! The fixed-threshold optimization primitive with its actual public
translated Gaussian learner, raw-call cap, and extended-loss guarantee. -/
noncomputable section
open MeasureTheory Set
open scoped Classical

namespace HeavyTail

theorem gaussianStage_tuned_bound {θ : OracleParameters} {τ R α : ℝ} {n : ℕ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hR : 0 < R) (hn : 0 < n)
    (hα : 0 < α) (hα1 : α < 1 / 10) (hnlog : confidenceLog α ≤ (n : ℝ)) :
    gaussianStageErrorBound θ R τ (gaussianStageSmoothing R α) (gaussianStageStep θ τ R α n)
      (gaussianStageQuadratic θ τ R α n) (gaussianStageResidual θ τ R α n)
      (α / 4) (R / (8 * n)) n ≤
    acceptedStageConstant θ.p * R * fixedThresholdAmplitude θ.G θ.L θ.s θ.p α τ n := by
  have hm := online_master_bound (GaussianEstimates.mixedConstant_pos θ.p).le θ.p_gt_one
    (acceptedMeanScale_pos θ hτ) (acceptedTraceScale_pos θ hτ).le (acceptedWeakScale_pos θ)
    hR (confidenceLog_ge_one hα hα1) ((confidenceLog_ge_one hα hα1).trans hnlog)
  have hr := accepted_rate_bound θ hτ hα hα1 hR.le hnlog
  exact (gaussianStageErrorBound_le_onlineMaster hτ hR hn hα hα1).trans
    ((add_le_add_right (add_le_add_right hm _) _).trans hr)

namespace PrivateInstance
open GaussianEntropy
universe u
variable {E ι : Type u} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

theorem translatedGaussianPrimitive_loss (I : PrivateInstance B)
    {c : E} {R τ α : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (offsets : ι → E) (hball : ∀ i, ‖offsets i‖ ≤ R)
    (i₀ : ι) (hzero : offsets i₀ = 0)
    (hcover : ∀ u : E, ‖u‖ ≤ R → ∃ i, ‖offsets i - u‖ ≤ R / (8 * n))
    (hcenter : ‖c - I.minimizer‖ ≤ R)
    (P : Measure PUnit) [IsProbabilityMeasure P] (hα : 0 < α) (hα1 : α < 1 / 10)
    (hnlog : confidenceLog α ≤ (n : ℝ)) :
    let initial : SimplexPoint ι := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
    let hp := gaussianStage_parameters hτ hR hn hα hα1
    let L := translatedGaussianStageLearner c (gaussianStageSmoothing R α)
      (gaussianStageStep θ τ R α n) (gaussianStageQuadratic θ τ R α n)
      offsets hball initial hp.2.2.2.2.2
    ((B.cappedStagePolicy hR hn τ L (4 * n)).outputLaw P I.oracle).real
      {x | ENNReal.ofReal (acceptedStageConstant θ.p * R *
        fixedThresholdAmplitude θ.G θ.L θ.s θ.p α τ n) < I.loss x} ≤ α := by
  dsimp only
  have hp := gaussianStage_parameters hτ hR hn hα hα1
  let initial : SimplexPoint ι := ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
  let L := translatedGaussianStageLearner c (gaussianStageSmoothing R α)
    (gaussianStageStep θ τ R α n) (gaussianStageQuadratic θ τ R α n)
    offsets hball initial hp.2.2.2.2.2
  have ht := I.translatedGaussianStage_loss_confidence hR hn hτ offsets hball i₀ hzero hcover
    hcenter hp.2.2.1 hp.2.2.2.1 hp.1 hp.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    (show 0 ≤ R / (8 * (n : ℝ)) by positivity) P hα hnlog
  have hb := gaussianStage_tuned_bound hτ hR hn hα hα1 hnlog
  apply le_trans (measureReal_mono (μ := (B.cappedStagePolicy hR hn τ L (4 * n)).outputLaw P I.oracle) ?_) ht
  intro x hx
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hb) hx

end PrivateInstance
end HeavyTail
