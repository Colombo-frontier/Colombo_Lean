import NCConcave16991.OracleProgramProbability
import NCConcave16991.TheoremStatements

/-! # Transfer of actual interactive-program integrals to the oracle model -/

open MeasureTheory
open scoped ENNReal

namespace NCConcave16991.OracleProgram

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  {Ω : Type} [MeasurableSpace Ω] {T : ℕ}

theorem squaredExpectationGuarantee_iff
    (Q : ProblemProgram K (n := p.n) (dx := dx) Ω T)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (P : Problem p dx dy K) :
    SquaredExpectationGuarantee (randomizedPolicy K Q ν) P T ↔
      (∀ seed, DifferentiableAt ℝ (problemMoreauEnvelope P) (eval Q (oracleResponse P) seed)) ∧
      Integrable (fun seed ↦ ‖gradient (problemMoreauEnvelope P) (eval Q (oracleResponse P) seed)‖ ^ 2) ν ∧
      (∫ seed, ‖gradient (problemMoreauEnvelope P) (eval Q (oracleResponse P) seed)‖ ^ 2 ∂ν) <
        p.epsilon ^ 2 / 200 := by
  change ((∀ seed, DifferentiableAt ℝ (problemMoreauEnvelope P)
      (OraclePolicy.run K (compile K Q) (oracleResponse P) seed T).1) ∧
      Integrable (fun seed ↦ ‖gradient (problemMoreauEnvelope P)
        (OraclePolicy.run K (compile K Q) (oracleResponse P) seed T).1‖ ^ 2) ν ∧
      (∫ seed, ‖gradient (problemMoreauEnvelope P)
        (OraclePolicy.run K (compile K Q) (oracleResponse P) seed T).1‖ ^ 2 ∂ν) <
          p.epsilon ^ 2 / 200) ↔ _
  simp only [run_output_eq_eval]

theorem successAtProbability_iff
    (Q : ProblemProgram K (n := p.n) (dx := dx) Ω T)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (P : Problem p dx dy K) (probability : ℝ≥0∞) :
    SuccessAtProbability (randomizedPolicy K Q ν) P T probability ↔
      MeasurableSet {seed | StationaryOutput P (eval Q (oracleResponse P) seed)} ∧
        probability ≤ ν {seed | StationaryOutput P (eval Q (oracleResponse P) seed)} := by
  change (MeasurableSet {seed | StationaryOutput P
      (OraclePolicy.run K (compile K Q) (oracleResponse P) seed T).1} ∧
      probability ≤ ν {seed | StationaryOutput P
        (OraclePolicy.run K (compile K Q) (oracleResponse P) seed T).1}) ↔ _
  simp only [run_output_eq_eval]

end

end NCConcave16991.OracleProgram
