import InformativeHandleCount

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Task006.Full
namespace OracleAlgorithm
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- Exact predictable-selection identity, before the deterministic reply bound
is applied. The oracle feedback may be any jointly measurable real function. -/
theorem expected_weighted_handles_ennreal_eq (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (seed : S) (z : Ω)
    (w : Ω → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    (∫⁻ tape, A.weightedHandles F seed w tape ∂iidHandleLaw μ) =
      ENNReal.ofReal (∫ x, w x ∂μ) *
        (∫⁻ tape, ((A.queriedHandles F tape seed).card : ℝ≥0∞) ∂iidHandleLaw μ) := by
  have hp : 0 ≤ ∫ x, w x ∂μ := integral_nonneg hw0
  have hterm (h : ℕ) :
      (∫⁻ tape, ENNReal.ofReal (w (tape h) * A.queriedIndicator F seed h tape)
        ∂iidHandleLaw μ) = ENNReal.ofReal (∫ x, w x ∂μ) *
          (iidHandleLaw μ) {tape | A.queriedBefore F tape seed h N} := by
    have hm := (hw.comp (measurable_pi_apply h)).mul
      (A.queriedIndicator_measurable F hF seed h)
    have hn (tape : ℕ → Ω) : 0 ≤ w (tape h) * A.queriedIndicator F seed h tape :=
      mul_nonneg (hw0 _) (A.queriedIndicator_nonneg F seed h tape)
    have hb (tape : ℕ → Ω) : w (tape h) * A.queriedIndicator F seed h tape ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right (hw1 _) (A.queriedIndicator_nonneg F seed h tape)).trans
        (by simpa using A.queriedIndicator_le_one F seed h tape)
    have hint : Integrable (fun tape => w (tape h) * A.queriedIndicator F seed h tape)
        (iidHandleLaw μ) := Integrable.of_bound hm.aestronglyMeasurable 1
          (Filter.Eventually.of_forall (fun tape => by
            rw [Real.norm_eq_abs,abs_of_nonneg (hn tape)]; exact hb tape))
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hn),
      A.queried_handle_factorization F hF μ seed h z w hw,
      ENNReal.ofReal_mul hp, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  unfold weightedHandles
  rw [lintegral_tsum (μ := iidHandleLaw μ)
    (f := fun h tape => ENNReal.ofReal (w (tape h) * A.queriedIndicator F seed h tape))
    (fun h => ((hw.comp (measurable_pi_apply h)).mul
      (A.queriedIndicator_measurable F hF seed h)).ennreal_ofReal.aemeasurable)]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left]
  congr 1
  simp_rw [← A.tsum_queriedIndicator F seed]
  rw [lintegral_tsum (fun h =>
    (A.queriedIndicator_measurable F hF seed h).ennreal_ofReal.aemeasurable)]
  simp_rw [A.lintegral_query_indicator F hF μ seed]

/-- Literal L5: informative paid handles have expectation p times the number
of distinct paid-accessed handles, even under arbitrary adaptive selection. -/
theorem expected_informativeHandles_eq (A : OracleAlgorithm d N S)
    (F : Space d → ℝ → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (seed : S) :
    (∫ tape, ((A.informativeHandles F tape seed).card : ℝ) ∂iidHandleLaw μ) =
      (∫ g, nonzeroStatus g ∂μ) *
        (∫ tape, ((A.queriedHandles F tape seed).card : ℝ) ∂iidHandleLaw μ) := by
  have he := A.expected_weighted_handles_ennreal_eq F hF μ seed 0 nonzeroStatus
    nonzeroStatus_measurable nonzeroStatus_nonneg nonzeroStatus_le_one
  have hm : Measurable (fun tape => ((A.queriedHandles F tape seed).card : ℝ≥0∞)) := by
    simp_rw [← A.tsum_queriedIndicator F seed]
    exact Measurable.ennreal_tsum (fun h =>
      (A.queriedIndicator_measurable F hF seed h).ennreal_ofReal)
  have hfinite (tape : ℕ → ℝ) :
      ((A.queriedHandles F tape seed).card : ℝ≥0∞) < ∞ := by simp
  have hfiniteW (tape : ℕ → ℝ) : A.weightedHandles F seed nonzeroStatus tape < ∞ := by
    rw [A.weightedHandles_nonzero_eq F seed]; simp
  have hleft := integral_toReal (μ := iidHandleLaw μ)
    (A.weightedHandles_measurable F hF seed nonzeroStatus nonzeroStatus_measurable).aemeasurable
    (Filter.Eventually.of_forall hfiniteW)
  have hright := integral_toReal (μ := iidHandleLaw μ) hm.aemeasurable (Filter.Eventually.of_forall hfinite)
  rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg nonzeroStatus_nonneg)] at hleft
  simpa only [A.weightedHandles_nonzero_eq, ENNReal.toReal_natCast, ← hright] using hleft

#print axioms expected_weighted_handles_ennreal_eq
#print axioms expected_informativeHandles_eq
end
end OracleAlgorithm
end Task006.Full
