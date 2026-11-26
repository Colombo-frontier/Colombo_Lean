import NCConcave16991.AcceleratedProgramOuter
import NCConcave16991.OracleProgramGuarantees
import NCConcave16991.UpperAssembly

/-! # The uniform fixed-budget accelerated upper bound of Theorem 3.2 -/

open Set MeasureTheory
open scoped ENNReal

namespace NCConcave16991

noncomputable section

theorem accelerated_validThreeQuartersBudget (p : ProblemParameters) :
    ValidThreeQuartersBudget p (Accelerated.publicAcceleratedBudget p) := by
  classical
  intro dx dy K x0
  let y0 : DualSpace dy := Classical.choose K.nonempty
  have hy0 : y0 ∈ K.carrier := Classical.choose_spec K.nonempty
  let Q := AcceleratedProgram.selectedOuterProgram (p := p) (dx := dx) y0 hy0 x0
  let A := OracleProgram.randomizedPolicy K Q (Accelerated.outerOutputLaw p)
  refine ⟨A, ?_⟩
  intro P h0 hAS
  apply (OracleProgram.successAtProbability_iff Q (Accelerated.outerOutputLaw p) P (3 / 4)).2
  have he (ω : Accelerated.OuterHistory p × Fin (Accelerated.outerHorizon p)) :
      OracleProgram.eval Q (oracleResponse P) ω = Accelerated.outerOutput P hAS y0 hy0 ω :=
    AcceleratedProgram.eval_selectedOuterProgram P hAS y0 hy0 x0 h0 ω
  simp_rw [he]
  refine ⟨(Set.to_countable _).measurableSet, ?_⟩
  have hh := (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top (Accelerated.outerOutputLaw p)
      {ω | StationaryOutput P (Accelerated.outerOutput P hAS y0 hy0 ω)})).2
    (Accelerated.outer_stationarity_probability P hAS y0 hy0)
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
    ENNReal.ofReal_ofNat] at hh
  exact hh

theorem accelerated_upper (p : ProblemParameters) :
    ∃ budget : ℕ, ValidThreeQuartersBudget p budget ∧
      (budget : ℝ) ≤ (2 : ℝ) ^ 48 * (1 + dimensionlessA p) *
        ((p.n : ℝ) + (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p) * complexityLog p := by
  exact ⟨Accelerated.publicAcceleratedBudget p, accelerated_validThreeQuartersBudget p,
    Accelerated.publicAcceleratedBudget_bound p⟩

theorem accelerated_validBudget (p : ProblemParameters) :
    ValidBudget p .averaged (Accelerated.publicAcceleratedBudget p) :=
  validBudget_of_threeQuarters (accelerated_validThreeQuartersBudget p)

end

end NCConcave16991
