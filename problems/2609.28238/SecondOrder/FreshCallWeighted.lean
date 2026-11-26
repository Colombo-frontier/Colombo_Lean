import SecondOrder.PostMoveConfidence

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace SecondOrder
noncomputable section

/-- The total predictable charge along an actual sampled history. Each
charge is chosen from the old history, before the new sample is read. -/
def freshCharge {Ω : Type*} (c : (n : ℕ) → Draws Ω n → ℝ≥0∞) :
    (n : ℕ) → Draws Ω n → ℝ≥0∞
  | 0, _ => 0
  | n+1, w => freshCharge c n w.1+c n w.1

theorem freshCharge_measurable {Ω : Type*} [MeasurableSpace Ω]
    (c : (n : ℕ) → Draws Ω n → ℝ≥0∞) (hc : ∀ n, Measurable (c n)) (n : ℕ) :
    Measurable (freshCharge c n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).add ((hc n).comp measurable_fst)

theorem freshCharge_integral_succ {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c : (n : ℕ) → Draws Ω n → ℝ≥0∞) (hc : ∀ n, Measurable (c n)) (n : ℕ) :
    (∫⁻ w, freshCharge c (n+1) w ∂drawsLaw μ (n+1)) =
      (∫⁻ w, freshCharge c n w ∂drawsLaw μ n)+(∫⁻ w, c n w ∂drawsLaw μ n) := by
  change (∫⁻ w, freshCharge c n w.1+c n w.1 ∂(drawsLaw μ n).prod μ) = _
  have hm : Measurable (fun w : Draws Ω n × Ω => freshCharge c n w.1+c n w.1) :=
    ((freshCharge_measurable c hc n).comp measurable_fst).add ((hc n).comp measurable_fst)
  rw [lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_const,measure_univ,mul_one]
  exact lintegral_add_left (freshCharge_measurable c hc n) _

/-- A conditional union bound with history-dependent charges. It pays the
expectation of the actual cumulative charge, rather than a worst-case
charge at each step. The failure events need not be independent. -/
theorem fresh_calls_weighted_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B : FreshCallFailure Ω) (c : (n : ℕ) → Draws Ω n → ℝ≥0∞)
    (hB : ∀ n, MeasurableSet {w : Draws Ω n × Ω | B n w.1 w.2})
    (hc : ∀ n, Measurable (c n)) (hb : ∀ n w, μ {z | B n w z} ≤ c n w) (N : ℕ) :
    drawsLaw μ N {w | ¬freshHistoryGood B N w} ≤
      ∫⁻ w, freshCharge c N w ∂drawsLaw μ N := by
  induction N with
  | zero => simp [freshHistoryGood,freshCharge]
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
    have hnew : drawsLaw μ (n+1) {w | B n w.1 w.2} ≤ ∫⁻ w, c n w ∂drawsLaw μ n := by
      simpa only [Set.mem_univ,true_and,Measure.restrict_univ] using
        fresh_event_past_variable_bound (η := drawsLaw μ n) (hB n) (hb n) MeasurableSet.univ
    rw [he,freshCharge_integral_succ c hc n]
    exact (measure_union_le _ _).trans (add_le_add (hold ▸ ih) hnew)

theorem fresh_calls_path_charge_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B : FreshCallFailure Ω) (c : (n : ℕ) → Draws Ω n → ℝ≥0∞)
    (hB : ∀ n, MeasurableSet {w : Draws Ω n × Ω | B n w.1 w.2})
    (hc : ∀ n, Measurable (c n)) (hb : ∀ n w, μ {z | B n w z} ≤ c n w)
    (N : ℕ) {C : ℝ≥0∞} (hC : ∀ w, freshCharge c N w ≤ C) :
    drawsLaw μ N {w | ¬freshHistoryGood B N w} ≤ C := by
  apply (fresh_calls_weighted_bound B c hB hc hb N).trans
  exact (lintegral_mono hC).trans_eq (by simp)

end
end SecondOrder
