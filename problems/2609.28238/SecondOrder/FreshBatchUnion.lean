import SecondOrder.FreshCallWeighted

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- Actual charge of a batch may depend on its fresh outcomes (for
example, a curvature certificate suppresses all post-move calls). -/
def freshBatchCharge {Ω : Type*} (c : (n : ℕ) → Draws Ω n × Ω → ℝ≥0∞) :
    (n : ℕ) → Draws Ω n → ℝ≥0∞
  | 0, _ => 0
  | n+1, w => freshBatchCharge c n w.1+c n w

theorem freshBatchCharge_measurable {Ω : Type*} [MeasurableSpace Ω]
    (c : (n : ℕ) → Draws Ω n × Ω → ℝ≥0∞) (hc : ∀ n, Measurable (c n)) (n : ℕ) :
    Measurable (freshBatchCharge c n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).add (hc n)

theorem freshBatchCharge_integral_succ {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : (n : ℕ) → Draws Ω n × Ω → ℝ≥0∞) (hc : ∀ n, Measurable (c n)) (n : ℕ) :
    (∫⁻ w, freshBatchCharge c (n+1) w ∂drawsLaw μ (n+1)) =
      (∫⁻ w, freshBatchCharge c n w ∂drawsLaw μ n)+
        (∫⁻ w, c n w ∂(drawsLaw μ n).prod μ) := by
  have hm : Measurable (fun w : Draws Ω n × Ω => freshBatchCharge c n w.1) :=
    (freshBatchCharge_measurable c hc n).comp measurable_fst
  change (∫⁻ w, freshBatchCharge c n w.1+c n w ∂(drawsLaw μ n).prod μ) = _
  rw [lintegral_add_left hm,lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_const,measure_univ,mul_one]

/-- Slice failure is bounded by the expected actual batch charge. Summing
on the recursive product history gives the expected actual total charge,
even when a fresh result decides whether later calls in a batch occur. -/
theorem fresh_batches_union_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B : FreshCallFailure Ω) (c : (n : ℕ) → Draws Ω n × Ω → ℝ≥0∞)
    (hB : ∀ n, MeasurableSet {w : Draws Ω n × Ω | B n w.1 w.2})
    (hc : ∀ n, Measurable (c n))
    (hb : ∀ n w, μ {z | B n w z} ≤ ∫⁻ z, c n (w,z) ∂μ) (N : ℕ) :
    drawsLaw μ N {w | ¬freshHistoryGood B N w} ≤
      ∫⁻ w, freshBatchCharge c N w ∂drawsLaw μ N := by
  induction N with
  | zero => simp [freshHistoryGood,freshBatchCharge]
  | succ n ih =>
    have he : {w : Draws Ω (n+1) | ¬freshHistoryGood B (n+1) w} =
        {w | ¬freshHistoryGood B n w.1} ∪ {w | B n w.1 w.2} := by
      ext w
      simp only [freshHistoryGood,Set.mem_setOf_eq,Set.mem_union]
      tauto
    have hold : drawsLaw μ (n+1) {w | ¬freshHistoryGood B n w.1} =
        drawsLaw μ n {w | ¬freshHistoryGood B n w} := by
      have hs : {w : Draws Ω (n+1) | ¬freshHistoryGood B n w.1} =
          {w | ¬freshHistoryGood B n w} ×ˢ Set.univ := by
        ext w
        change (¬freshHistoryGood B n w.1) ↔ (¬freshHistoryGood B n w.1) ∧ True
        simp
      rw [hs]
      change ((drawsLaw μ n).prod μ) (_ ×ˢ Set.univ) = _
      simp
    have hnew : drawsLaw μ (n+1) {w | B n w.1 w.2} ≤ ∫⁻ w, c n w ∂(drawsLaw μ n).prod μ := by
      rw [lintegral_prod _ (hc n).aemeasurable]
      simpa only [Set.mem_univ,true_and,Measure.restrict_univ] using
        fresh_event_past_variable_bound (η := drawsLaw μ n) (hB n) (hb n) MeasurableSet.univ
    rw [he,freshBatchCharge_integral_succ c hc n]
    exact (measure_union_le _ _).trans (add_le_add (hold ▸ ih) hnew)

theorem fresh_batches_path_charge_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B : FreshCallFailure Ω) (c : (n : ℕ) → Draws Ω n × Ω → ℝ≥0∞)
    (hB : ∀ n, MeasurableSet {w : Draws Ω n × Ω | B n w.1 w.2})
    (hc : ∀ n, Measurable (c n))
    (hb : ∀ n w, μ {z | B n w z} ≤ ∫⁻ z, c n (w,z) ∂μ)
    (N : ℕ) {C : ℝ≥0∞} (hC : ∀ w, freshBatchCharge c N w ≤ C) :
    drawsLaw μ N {w | ¬freshHistoryGood B N w} ≤ C := by
  apply (fresh_batches_union_bound B c hB hc hb N).trans
  exact (lintegral_mono hC).trans_eq (by simp)

end
end SecondOrder
