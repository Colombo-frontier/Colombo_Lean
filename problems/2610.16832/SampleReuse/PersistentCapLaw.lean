import SampleReuse.PersistentTapeEvents
import SampleReuse.PersistentStoppingExpectation

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section
variable {Q H Y O S Ξ Z : Type} [MeasurableSpace Ξ]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The finite-slot law used in hardness proofs is exactly the cap-output
law of the genuine infinite iid oracle and independent private coins. -/
theorem lazyPersistentOutput_probability (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (Q × H) Y O S) (reply : Q → Z → Y) (p : PMF Z)
    (N : ℕ) (success : O → Prop)
    (hE : ∀ table : Fin (N+1) → Z, MeasurableSet {ξ | success
      ((normalizePersistentAlgorithm N (P ξ)).output N
        (persistentQueryRun (normalizePersistentAlgorithm N (P ξ)).toQueryPolicy reply table N))}) :
    (μ.prod (iidSampleTapeLaw p)).real {w : Ξ × (ℕ → Z) | success
      ((P w.1).output N (lazyPersistentRun (P w.1).toQueryPolicy reply w.2 N).1)} =
    ∫ ξ, pmfEventProbability (finitePiPMF (fun _ : Fin (N+1) => p)) (fun table => decide
      (success ((normalizePersistentAlgorithm N (P ξ)).output N
        (persistentQueryRun (normalizePersistentAlgorithm N (P ξ)).toQueryPolicy reply table N)))) ∂μ := by
  let E : Ξ → (Fin (N+1) → Z) → Prop := fun ξ table => success
    ((normalizePersistentAlgorithm N (P ξ)).output N
      (persistentQueryRun (normalizePersistentAlgorithm N (P ξ)).toQueryPolicy reply table N))
  have he : {w : Ξ × (ℕ → Z) | success
      ((P w.1).output N (lazyPersistentRun (P w.1).toQueryPolicy reply w.2 N).1)} =
      {w : Ξ × (ℕ → Z) | E w.1 (fun i => w.2 i.val)} := by
    ext w
    simp only [Set.mem_setOf_eq,E]
    rw [normalizePersistentAlgorithm_output N (P w.1) reply _ w.2 (fun _ => rfl)]
  rw [he]
  exact iidSampleTapeLaw_event_probability μ p (N+1) E hE

theorem persistent_expected_calls_from_finite_cap (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm Q H Y O S) (reply : Q → Z → Y) (p : PMF Z)
    (N : ℕ) (success : O → Prop)
    (hs : ∀ n, Measurable (fun w : Ξ × (ℕ → Z) => (P w.1).stopOnRun reply w.2 n))
    (hE : ∀ table : Fin (N+1) → Z, MeasurableSet {ξ | success
      ((normalizePersistentAlgorithm N (P ξ).cap).output N
        (persistentQueryRun (normalizePersistentAlgorithm N (P ξ).cap).toQueryPolicy reply table N))})
    {a δ : ℝ}
    (hsolve : a ≤ (μ.prod (iidSampleTapeLaw p)).real {w : Ξ × (ℕ → Z) |
      (P w.1).Halts reply w.2 ∧ success ((P w.1).outputFor reply w.2)})
    (hcap : (∫ ξ, pmfEventProbability (finitePiPMF (fun _ : Fin (N+1) => p)) (fun table => decide
      (success ((normalizePersistentAlgorithm N (P ξ).cap).output N
        (persistentQueryRun (normalizePersistentAlgorithm N (P ξ).cap).toQueryPolicy reply table N)))) ∂μ) ≤ δ) :
    (N+1:ℕ) * ENNReal.ofReal (a-δ) ≤
      ∫⁻ w : Ξ × (ℕ → Z), (P w.1).extendedCost reply w.2 ∂μ.prod (iidSampleTapeLaw p) := by
  apply PersistentStoppingAlgorithm.extended_expected_calls_from_cap (fun w => P w.1) reply
    (fun w => w.2) hs (μ.prod (iidSampleTapeLaw p)) success N hsolve
  rw [lazyPersistentOutput_probability μ (fun ξ => (P ξ).cap) reply p N success hE]
  exact hcap

end
end SampleReuse
