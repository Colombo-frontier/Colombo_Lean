import SampleReuse.PersistentHandleLaw
import SampleReuse.PaddingOracle

open SecondOrder MeasureTheory
open scoped Classical
namespace SampleReuse
noncomputable section

theorem persistentQueryRun_scalar {Z H S : Type} {d : ℕ}
    (P : QueryPolicy (Point d × H) (RichReply d) S)
    (F : Z → Point d → ℝ) (table : H → Z) : ∀ n,
    persistentQueryRun P (fun x z => richReply F z x) table n =
      persistentScalarRun P F table n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [persistentQueryRun,persistentScalarRun,ih]

/-- Actual scalar value, gradient and Hessian replies under the source's
persistent oracle. The transformed program has no access to latent samples. -/
theorem normalized_rich_output_law {Z H S O : Type} [Fintype Z] {d : ℕ} (N : ℕ)
    (P : OracleAlgorithm (Point d × H) (RichReply d) O S)
    (F : Z → Point d → ℝ) (p : PMF Z) :
    (finitePiPMF (fun _ : Fin (N+1) => p)).map
      (fun table => (normalizePersistentAlgorithm N P).output N
        (persistentScalarRun (normalizePersistentAlgorithm N P).toQueryPolicy F table N)) =
      lazyPersistentOutputLaw P (fun x z => richReply F z x) p N := by
  simpa only [persistentQueryRun_scalar] using
    normalized_persistent_output_law N P (fun x z => richReply F z x) p

/-- Exact success-event probability, without any additional regularity
condition on the original labels or the algorithm's private state. -/
theorem normalized_rich_event_probability {Z H S O : Type} [Fintype Z] {d : ℕ} (N : ℕ)
    (P : OracleAlgorithm (Point d × H) (RichReply d) O S)
    (F : Z → Point d → ℝ) (p : PMF Z) (success : Set O) :
    (finitePiPMF (fun _ : Fin (N+1) => p)).toOuterMeasure
      {table | (normalizePersistentAlgorithm N P).output N
        (persistentScalarRun (normalizePersistentAlgorithm N P).toQueryPolicy F table N) ∈ success} =
      (lazyPersistentOutputLaw P (fun x z => richReply F z x) p N).toOuterMeasure success := by
  have hm := PMF.toOuterMeasure_map_apply
    (fun table => (normalizePersistentAlgorithm N P).output N
      (persistentScalarRun (normalizePersistentAlgorithm N P).toQueryPolicy F table N))
    (finitePiPMF (fun _ : Fin (N+1) => p)) success
  rw [normalized_rich_output_law] at hm
  exact hm.symm

end
end SampleReuse
