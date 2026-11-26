import SampleReuse.MarginalGradientRate
import SampleReuse.OptionTableObservation

open SecondOrder MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

namespace SampleReuse
noncomputable section

variable {Ξ S Handle : Type} {d : ℕ} {R : ℝ} [Fintype Handle]
  [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle] [MeasurableSingletonClass Handle]

local instance marginalTable_option_measurable : MeasurableSpace (Option Handle) := ⊤
local instance marginalTable_option_singleton : MeasurableSingletonClass (Option Handle) := ⟨fun _ => trivial⟩

def marginalHistoryObservation
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (N : ℕ) (h : FiniteHistory Ξ (SignedCoefficient R) N) : ℕ × Point d :=
  (marginalHistoryGradientCount (fun ξ => (P ξ).toQueryPolicy) ε v N h,
    marginalHistoryOutput P ε v N h)

/-- Actual gradient calls and output under an immutable scalar sample table. -/
def marginalTableObservation
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (N : ℕ) (z : Ξ × (Handle → SignedCoefficient R)) : ℕ × Point d :=
  (∑ k ∈ Finset.range N,
    if ((P z.1).query k (marginalPersistentRun (P z.1).toQueryPolicy ε v z.2 k)).1 then 1 else 0,
    (P z.1).output N (marginalPersistentRun (P z.1).toQueryPolicy ε v z.2 N))

omit [Fintype Handle] [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle]
  [MeasurableSingletonClass Handle] in
theorem marginalObservation_table
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (N : ℕ) (ξ : Ξ) (table : Handle → SignedCoefficient R)
    (a₀ : SignedCoefficient R) :
    marginalHistoryObservation P ε v N
      (tableHistory (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
        ξ (extendOptionTable a₀ table) N) = marginalTableObservation P ε v N (ξ,table) := by
  have he : extendOptionTable a₀ table = marginalExtendedTable table a₀ := by
    funext key
    cases key <;> rfl
  rw [he]
  exact Prod.ext (marginalHistoryGradientCount_table _ ε v ξ table a₀ N)
    (marginalHistoryOutput_table P ε v ξ table a₀ N)

omit [Fintype Handle] [MeasurableSingletonClass Handle] in
theorem marginalHistoryObservation_measurable
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (N : ℕ) :
    Measurable (marginalHistoryObservation (R := R) P ε v N) :=
  (marginalHistoryGradientCount_measurable _ hP.toMeasurableQueryPolicyFamily ε v N).prodMk
    (marginalHistoryOutput_measurable P hP ε v N)

theorem marginalTableObservation_measurable
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (N : ℕ) :
    Measurable (marginalTableObservation (R := R) P ε v N) := by
  let a₀ : SignedCoefficient R := ⟨R,by simp⟩
  have ht := tableHistory_measurable (marginalHistoryKey (R := R) (fun ξ => (P ξ).toQueryPolicy) ε v)
    (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v) N
  have hh := (marginalHistoryObservation_measurable P hP ε v N).comp
    (ht.comp (measurable_fst.prodMk
      ((measurable_of_countable (extendOptionTable a₀)).comp measurable_snd)))
  have he : (fun z : Ξ × (Handle → SignedCoefficient R) =>
      marginalHistoryObservation P ε v N
        (tableHistory (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
          z.1 (extendOptionTable a₀ z.2) N)) = marginalTableObservation P ε v N :=
    funext (fun z => marginalObservation_table P ε v N z.1 z.2 a₀)
  exact he ▸ hh

/-- Joint equality of the actual output and gradient-call distribution.
Every real handle is sampled once from the original scalar-loss sample law. -/
theorem marginal_table_observation_law (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (hR : 2 ≤ R)
    (θ : Bool) (N : ℕ) :
    (marginalOracleLaw μ P hP ε v hR θ N).map (marginalHistoryObservation P ε v N) =
      (μ.prod (finitePiPMF (fun _ : Handle =>
        coefficientPMF R (signValue θ) hR (signValue_sq θ))).toMeasure).map
        (marginalTableObservation P ε v N) := by
  have hp : marginalCoefficientLaw hR θ = (fun key : Option Handle =>
      key.elim (fairCoefficientPMF R hR) (fun _ => coefficientPMF R (signValue θ) hR (signValue_sq θ))) := by
    funext key
    cases key <;> rfl
  unfold marginalOracleLaw
  rw [hp]
  exact option_table_observation_law μ
    (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
    (marginalHistoryKey_measurable _ hP.toMeasurableQueryPolicyFamily ε v)
    (fairCoefficientPMF R hR) (fun _ => coefficientPMF R (signValue θ) hR (signValue_sq θ)) N
    (marginalHistoryObservation P ε v N) (marginalHistoryObservation_measurable P hP ε v N)
    (marginalTableObservation P ε v N) (marginalTableObservation_measurable P hP ε v N)
    (marginalObservation_table P ε v N)

end
end SampleReuse
