import SecondOrder.BinaryTracker
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder

/-- Union-bound guarantee for the concrete online tracker. The estimates may
be arbitrarily dependent; only their individual failure probabilities enter. -/
theorem binaryTracker_failure_probability {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (M : ℕ)
    (G : Ω → ℕ → E) (anchor : Ω → E)
    (packet : Ω → ℕ → BinaryNode (binaryDepth M) → E)
    {τ ρ : ℝ} (hρ : 0 ≤ ρ) (hb : (binaryDepth M : ℝ)*ρ ≤ τ/4)
    (δa : ℝ≥0∞) (δc : BinaryNode (binaryDepth M) → ℝ≥0∞)
    (ha : μ {w | τ/4 < ‖anchor w-G w 0‖} ≤ δa)
    (hc : ∀ i ∈ completedNodes (binaryDepth M) M,
      μ {w | ρ < ‖packet w (nodeRight i-1) i-(G w (nodeRight i)-G w (nodeLeft i))‖} ≤ δc i) :
    μ {w | ∃ n ≤ M, τ/2 < ‖binaryTracker (anchor w) (packet w) n-G w n‖} ≤
      δa+∑ i ∈ completedNodes (binaryDepth M) M, δc i := by
  let A : Set Ω := {w | τ/4 < ‖anchor w-G w 0‖}
  let B (i : BinaryNode (binaryDepth M)) : Set Ω :=
    {w | ρ < ‖packet w (nodeRight i-1) i-(G w (nodeRight i)-G w (nodeLeft i))‖}
  have hsub : {w | ∃ n ≤ M, τ/2 < ‖binaryTracker (anchor w) (packet w) n-G w n‖} ⊆
      A ∪ ⋃ i ∈ completedNodes (binaryDepth M) M, B i := by
    intro w hw
    by_contra hn
    have hna : ‖anchor w-G w 0‖ ≤ τ/4 := by
      have : w ∉ A := fun hh => hn (Or.inl hh)
      exact le_of_not_gt this
    have hnc : ∀ i ∈ completedNodes (binaryDepth M) M,
        ‖packet w (nodeRight i-1) i-(G w (nodeRight i)-G w (nodeLeft i))‖ ≤ ρ := by
      intro i hi
      apply le_of_not_gt
      intro hh
      apply hn
      exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hh⟩⟩)
    obtain ⟨n,hnM,hnerr⟩ := hw
    exact (not_lt_of_ge (binaryTracker_uniform_accuracy M (G w) (anchor w) (packet w)
      hρ hna hnc hb n hnM)) hnerr
  calc
    _ ≤ μ (A ∪ ⋃ i ∈ completedNodes (binaryDepth M) M, B i) := measure_mono hsub
    _ ≤ μ A+μ (⋃ i ∈ completedNodes (binaryDepth M) M, B i) := measure_union_le _ _
    _ ≤ δa+∑ i ∈ completedNodes (binaryDepth M) M, μ (B i) :=
      add_le_add ha (measure_biUnion_finset_le _ _)
    _ ≤ _ := add_le_add_left (Finset.sum_le_sum (fun i hi => hc i hi)) _

end SecondOrder
