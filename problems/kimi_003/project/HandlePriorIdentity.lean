import HandleExpectationIdentity
import ParameterizedHandleCount

open MeasureTheory
open scoped ENNReal
namespace Task006.Full.OracleAlgorithm
noncomputable section
variable {d N : ℕ} {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]

/-- Literal fresh-handle equality after averaging an independent prior and
private seed. No linearity, convexity or status-hiding property of F is needed. -/
theorem expected_informativeHandles_prior_eq (A : OracleAlgorithm d N S)
    (F : Z → Space d → ℝ → ℝ)
    (hF : Measurable (fun p : Z × (Space d × ℝ) => F p.1 p.2.1 p.2.2))
    (γ : Measure Z) [IsProbabilityMeasure γ]
    (seed : Z → S) (hseed : Measurable seed)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ w : Z × (ℕ → ℝ),
      ((A.informativeHandles (F w.1) w.2 (seed w.1)).card : ℝ)
        ∂γ.prod (iidHandleLaw μ)) =
      (∫ g, nonzeroStatus g ∂μ) *
      (∫ w : Z × (ℕ → ℝ),
      ((A.queriedHandles (F w.1) w.2 (seed w.1)).card : ℝ)
        ∂γ.prod (iidHandleLaw μ)) := by
  have hmap : Measurable (fun w : Z × (ℕ → ℝ) => ((w.1,seed w.1),w.2)) :=
    (measurable_fst.prodMk (hseed.comp measurable_fst)).prodMk measurable_snd
  have hK : Measurable (fun w : Z × (ℕ → ℝ) =>
      ((A.informativeHandles (F w.1) w.2 (seed w.1)).card : ℝ)) := by
    simpa only [Function.comp_def] using
      (A.informativeHandles_card_parameter_measurable F hF).comp hmap
  have hHenn : Measurable (fun w : (Z × S) × (ℕ → ℝ) =>
      ((A.queriedHandles (F w.1.1) w.2 w.1.2).card : ℝ≥0∞)) := by
    simp_rw [← A.tsum_queriedIndicator]
    apply Measurable.ennreal_tsum
    intro h
    exact (measurable_const.indicator
      (A.measurableSet_queriedBefore_parameter F hF h N)).ennreal_ofReal
  have hH : Measurable (fun w : Z × (ℕ → ℝ) =>
      ((A.queriedHandles (F w.1) w.2 (seed w.1)).card : ℝ)) := by
    simpa only [Function.comp_def,ENNReal.toReal_natCast] using hHenn.ennreal_toReal.comp hmap
  have hKi : Integrable (fun w : Z × (ℕ → ℝ) =>
      ((A.informativeHandles (F w.1) w.2 (seed w.1)).card : ℝ))
        (γ.prod (iidHandleLaw μ)) := by
    apply Integrable.of_bound hK.aestronglyMeasurable N
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast A.informativeHandles_card_le (F w.1) (seed w.1) w.2
  have hHi : Integrable (fun w : Z × (ℕ → ℝ) =>
      ((A.queriedHandles (F w.1) w.2 (seed w.1)).card : ℝ))
        (γ.prod (iidHandleLaw μ)) := by
    apply Integrable.of_bound hH.aestronglyMeasurable N
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast A.queriedHandles_card_le (F w.1) w.2 (seed w.1)
  rw [integral_prod _ hKi,integral_prod _ hHi,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact A.expected_informativeHandles_eq (F z)
    (hF.comp (measurable_const.prodMk measurable_id)) μ (seed z)

#print axioms expected_informativeHandles_prior_eq
end
end Task006.Full.OracleAlgorithm
