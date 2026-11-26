import SampleReuse.PersistentStopping

open MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse.PersistentStoppingAlgorithm
noncomputable section
variable {Q H Y O S Z Ω : Type*} [MeasurableSpace Ω]

theorem measurable_extendedCost (P : Ω → PersistentStoppingAlgorithm Q H Y O S)
    (reply : Q → Z → Y) (tape : Ω → ℕ → Z)
    (hs : ∀ n, Measurable (fun ω => (P ω).stopOnRun reply (tape ω) n)) :
    Measurable (fun ω => (P ω).extendedCost reply (tape ω)) := by
  apply Measurable.iSup
  intro n
  apply Measurable.ite _ measurable_const measurable_const
  change MeasurableSet {ω | ∀ k < n, (P ω).stopOnRun reply (tape ω) k = false}
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun k => MeasurableSet.iInter
    (fun _ => (hs k) (measurableSet_singleton false)))

/-- Fixed-cap hardness gives an expected evaluation lower bound for actual
persistent stopping algorithms, including nonhalting and infinite-cost runs. -/
theorem extended_expected_calls_from_cap
    (P : Ω → PersistentStoppingAlgorithm Q H Y O S)
    (reply : Q → Z → Y) (tape : Ω → ℕ → Z)
    (hs : ∀ n, Measurable (fun ω => (P ω).stopOnRun reply (tape ω) n))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (success : O → Prop)
    (N : ℕ) {p δ : ℝ}
    (hsuccess : p ≤ μ.real {ω | (P ω).Halts reply (tape ω) ∧
      success ((P ω).outputFor reply (tape ω))})
    (hcap : μ.real {ω | success ((P ω).cap.output N
      (lazyPersistentRun (P ω).cap.toQueryPolicy reply (tape ω) N).1)} ≤ δ) :
    (N+1:ℕ) * ENNReal.ofReal (p-δ) ≤ ∫⁻ ω, (P ω).extendedCost reply (tape ω) ∂μ := by
  have hsub : {ω | (P ω).Halts reply (tape ω) ∧ success ((P ω).outputFor reply (tape ω))} ⊆
      {ω | success ((P ω).cap.output N
        (lazyPersistentRun (P ω).cap.toQueryPolicy reply (tape ω) N).1)} ∪
      {ω | ((N+1:ℕ):ℝ≥0∞) ≤ (P ω).extendedCost reply (tape ω)} := by
    intro ω hω
    obtain ⟨hh,hout⟩ := hω
    by_cases hn : (P ω).cost reply (tape ω) ≤ N
    · left
      change success ((P ω).cap.output N (lazyPersistentRun (P ω).cap.toQueryPolicy reply (tape ω) N).1)
      rw [(P ω).cap_agrees reply (tape ω) hh N hn]
      exact hout
    · right
      change ((N+1:ℕ):ℝ≥0∞) ≤ (P ω).extendedCost reply (tape ω)
      rw [(P ω).extendedCost_eq_cost reply (tape ω) hh]
      exact_mod_cast (show N+1 ≤ (P ω).cost reply (tape ω) by omega)
  have hp : p-δ ≤ μ.real {ω | ((N+1:ℕ):ℝ≥0∞) ≤ (P ω).extendedCost reply (tape ω)} := by
    have hm := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
    linarith
  have he := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr hp
  exact (mul_le_mul_left' he ((N+1:ℕ):ℝ≥0∞)).trans
    (mul_meas_ge_le_lintegral (measurable_extendedCost P reply tape hs) ((N+1:ℕ):ℝ≥0∞))

end
end SampleReuse.PersistentStoppingAlgorithm
