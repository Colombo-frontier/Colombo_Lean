import SecondOrder.AdaptiveAnchor

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace SecondOrder
noncomputable section

/-- The failure of a new call may depend on all older samples. Calls after
an algorithm stops can be padded by the constantly false failure predicate. -/
abbrev FreshCallFailure (Ω : Type*) := (n : ℕ) → Draws Ω n → Ω → Prop

def freshHistoryGood {Ω : Type*} (B : FreshCallFailure Ω) : (n : ℕ) → Draws Ω n → Prop
  | 0, _ => True
  | n+1, w => freshHistoryGood B n w.1 ∧ ¬ B n w.1 w.2

theorem freshHistoryGood_measurableSet {Ω : Type*} [MeasurableSpace Ω] (B : FreshCallFailure Ω)
    (hB : ∀ n, MeasurableSet {w : Draws Ω n × Ω | B n w.1 w.2}) (n : ℕ) :
    MeasurableSet {w | freshHistoryGood B n w} := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact (ih.preimage measurable_fst).inter (hB n).compl

/-- A conditional union bound proved on the actual recursively sampled
history. Independence of the failure events is neither needed nor assumed. -/
theorem fresh_calls_union_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (B : FreshCallFailure Ω) (δ : ℕ → ℝ≥0∞)
    (hB : ∀ n, MeasurableSet {w : Draws Ω n × Ω | B n w.1 w.2})
    (hδ : ∀ n w, μ {z | B n w z} ≤ δ n) (N : ℕ) :
    drawsLaw μ N {w | ¬ freshHistoryGood B N w} ≤ ∑ n ∈ Finset.range N, δ n := by
  induction N with
  | zero => simp [freshHistoryGood]
  | succ n ih =>
    have he : {w : Draws Ω (n+1) | ¬ freshHistoryGood B (n+1) w} =
        {w | ¬ freshHistoryGood B n w.1} ∪ {w | B n w.1 w.2} := by
      ext w
      simp only [freshHistoryGood, Set.mem_setOf_eq, Set.mem_union]
      tauto
    have hold : drawsLaw μ (n+1) {w | ¬ freshHistoryGood B n w.1} =
        drawsLaw μ n {w | ¬ freshHistoryGood B n w} := by
      have hs : {w : Draws Ω (n+1) | ¬ freshHistoryGood B n w.1} =
          {w | ¬ freshHistoryGood B n w} ×ˢ Set.univ := by
        ext w
        change (¬ freshHistoryGood B n w.1) ↔ (¬ freshHistoryGood B n w.1) ∧ True
        simp
      rw [hs]
      change ((drawsLaw μ n).prod μ) ({w | ¬ freshHistoryGood B n w} ×ˢ Set.univ) = _
      simp
    have hnew : drawsLaw μ (n+1) {w | B n w.1 w.2} ≤ δ n := by
      simpa only [Set.mem_univ, true_and, measure_univ, mul_one] using
        fresh_event_past_bound (η := drawsLaw μ n) (μ := μ) (hB n) (hδ n) MeasurableSet.univ
    rw [he]
    calc
      _ ≤ drawsLaw μ (n+1) {w | ¬ freshHistoryGood B n w.1}+drawsLaw μ (n+1) {w | B n w.1 w.2} :=
        measure_union_le _ _
      _ ≤ (∑ i ∈ Finset.range n, δ i)+δ n := add_le_add (hold ▸ ih) hnew
      _ = _ := (Finset.sum_range_succ _ _).symm

theorem fresh_calls_constant_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (B : FreshCallFailure Ω) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hB : ∀ n, MeasurableSet {w : Draws Ω n × Ω | B n w.1 w.2})
    (hδ : ∀ n w, μ {z | B n w z} ≤ ENNReal.ofReal δ) (N : ℕ) :
    drawsLaw μ N {w | ¬ freshHistoryGood B N w} ≤ ENNReal.ofReal ((N : ℝ)*δ) := by
  have hh := fresh_calls_union_bound B (fun _ => ENNReal.ofReal δ) hB hδ N
  simpa [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast] using hh

end
end SecondOrder
