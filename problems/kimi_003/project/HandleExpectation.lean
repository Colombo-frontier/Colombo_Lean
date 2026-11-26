import HandleCount

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Task006.Full
namespace OracleAlgorithm

noncomputable section

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

def weightedHandles (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (seed : S) (w : Ω → ℝ) (tape : ℕ → Ω) : ℝ≥0∞ :=
  ∑' h, ENNReal.ofReal (w (tape h) * A.queriedIndicator F seed h tape)

theorem weightedHandles_measurable (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (seed : S) (w : Ω → ℝ) (hw : Measurable w) :
    Measurable (A.weightedHandles F seed w) := by
  apply Measurable.ennreal_tsum
  intro h
  exact ((hw.comp (measurable_pi_apply h)).mul
    (A.queriedIndicator_measurable F hF seed h)).ennreal_ofReal

theorem weightedHandles_le (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (seed : S) (w : Ω → ℝ) (hw : ∀ z, w z ≤ 1) (tape : ℕ → Ω) :
    A.weightedHandles F seed w tape ≤ (N : ℝ≥0∞) := by
  calc
    _ ≤ ∑' h, ENNReal.ofReal (A.queriedIndicator F seed h tape) := by
      apply ENNReal.tsum_le_tsum
      intro h
      apply ENNReal.ofReal_le_ofReal
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw (tape h))
        (A.queriedIndicator_nonneg F seed h tape)
    _ ≤ _ := A.tsum_queriedIndicator_le F seed tape

theorem lintegral_query_indicator (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (seed : S) (h : ℕ) :
    (∫⁻ tape, ENNReal.ofReal (A.queriedIndicator F seed h tape) ∂iidHandleLaw μ) =
      (iidHandleLaw μ) {tape | A.queriedBefore F tape seed h N} := by
  have hs : MeasurableSet {tape | A.queriedBefore F tape seed h N} :=
    (A.measurableSet_queriedBefore F hF h N).preimage
    (measurable_const.prodMk measurable_id)
  have heq : (fun tape => ENNReal.ofReal (A.queriedIndicator F seed h tape)) =
      {tape | A.queriedBefore F tape seed h N}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    classical
    funext tape
    by_cases hq : A.queriedBefore F tape seed h N <;> simp [queriedIndicator,Set.indicator,hq]
  rw [heq,lintegral_indicator hs]
  simp

theorem expected_weighted_handles_ennreal (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (seed : S) (z : Ω)
    (w : Ω → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    (∫⁻ tape, A.weightedHandles F seed w tape ∂iidHandleLaw μ) ≤
      ENNReal.ofReal (∫ x, w x ∂μ) * (N : ℝ≥0∞) := by
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
  have hsum : (∑' h, (iidHandleLaw μ) {tape | A.queriedBefore F tape seed h N}) ≤
      (N : ℝ≥0∞) := by
    simp_rw [← A.lintegral_query_indicator F hF μ seed]
    rw [← lintegral_tsum (fun h =>
      (A.queriedIndicator_measurable F hF seed h).ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ _tape : ℕ → Ω, (N : ℝ≥0∞) ∂iidHandleLaw μ :=
        lintegral_mono (A.tsum_queriedIndicator_le F seed)
      _ = _ := by simp
  unfold weightedHandles
  rw [lintegral_tsum (μ := iidHandleLaw μ)
    (f := fun h tape => ENNReal.ofReal (w (tape h) * A.queriedIndicator F seed h tape))
    (fun h => ((hw.comp (measurable_pi_apply h)).mul
      (A.queriedIndicator_measurable F hF seed h)).ennreal_ofReal.aemeasurable)]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul_left' hsum _

theorem expected_weighted_handles (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (seed : S) (z : Ω)
    (w : Ω → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    (∫ tape, (A.weightedHandles F seed w tape).toReal ∂iidHandleLaw μ) ≤
      (∫ x, w x ∂μ) * N := by
  rw [integral_toReal (A.weightedHandles_measurable F hF seed w hw).aemeasurable
    (Filter.Eventually.of_forall (fun tape =>
      (A.weightedHandles_le F seed w hw1 tape).trans_lt (by simp)))]
  have he := A.expected_weighted_handles_ennreal F hF μ seed z w hw hw0 hw1
  have ht : ENNReal.ofReal (∫ x, w x ∂μ) * (N : ℝ≥0∞) ≠ ∞ := by finiteness
  have hr := ENNReal.toReal_mono ht he
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg hw0),
    ENNReal.toReal_natCast] using hr

end
end OracleAlgorithm
end Task006.Full
