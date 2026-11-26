import NCConcave16991.OracleProgramCompiler

/-! # Private probability laws for compiled interactive oracle programs -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NCConcave16991.OracleProgram

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)
  {Ω : Type} [MeasurableSpace Ω] {T : ℕ}

/-- The program and its private seed law determine a genuine policy before the Problem is known. -/
def randomizedPolicy (P : ProblemProgram K (n := n) (dx := dx) Ω T)
    (ν : Measure Ω) [IsProbabilityMeasure ν] : RandomizedPolicy K (n := n) (dx := dx) where
  Seed := Ω
  seedSpace := inferInstance
  law := ν
  law_probability := inferInstance
  policy := compile K P

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter}

/-- Probability bounds on the independent program interpreter are exactly the model's Success. -/
theorem success_iff (P : ProblemProgram K' (n := p.n) (dx := dx) Ω T)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (F : Problem p dx dy K') :
    Success (randomizedPolicy K' P ν) F T ↔
      MeasurableSet {seed | StationaryOutput F (eval P (oracleResponse F) seed)} ∧
      (2 / 3 : ℝ≥0∞) ≤ ν {seed | StationaryOutput F (eval P (oracleResponse F) seed)} := by
  change (MeasurableSet {seed | StationaryOutput F
    (OraclePolicy.run K' (compile K' P) (oracleResponse F) seed T).1} ∧
      (2 / 3 : ℝ≥0∞) ≤ ν {seed | StationaryOutput F
        (OraclePolicy.run K' (compile K' P) (oracleResponse F) seed T).1}) ↔ _
  simp only [run_output_eq_eval]

end NCConcave16991.OracleProgram
