import RandomizedFO2003.ObstructionProbability

namespace RandomizedFO2003.Model

open MeasureTheory Cascade
open scoped BigOperators ENNReal

/-- The explicit constants and one finite dimension defeat every measurable
full-history randomized first-order algorithm below the stated rate. -/
theorem hard_dimension_below_rate {ε Δ L₁ L₂ : ℝ}
    (hε : 0 < ε) (hΔ : 0 < Δ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)))
    (T : ℕ) (hT : (T : ℝ) < parameterConstant * rate ε Δ L₁ L₂) :
    ∃ d : ℕ, ∀ (Seed : Type) [MeasurableSpace Seed]
      (ν : Measure Seed) [IsProbabilityMeasure ν] (A : Algorithm d Seed),
      ∃ f : Space d → ℝ, InFunctionClass f Δ L₁ L₂ ∧ ν (Success A f ε T) < (2 / 3 : ℝ≥0∞) := by
  obtain ⟨S⟩ := parameter_spectral_design hε hL₁ hL₂ hregime
  have hrate := parameter_stage_degree_rate hε hΔ hL₁ hL₂ hregime hmass
  have hsmall : T < stageIndex ε Δ L₂ * degreeCount ε L₁ L₂ := by
    exact_mod_cast hT.trans_le hrate
  have htime : T < (stageIndex ε Δ L₂ + 1) * degreeCount ε L₁ L₂ :=
    hsmall.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ _))
  obtain ⟨K, _htotal, hbudget⟩ := S.choose_terminal_budgets (lowerCurvature_pos hε hL₂)
    (rhsScale_pos hε) (stageIndex ε Δ L₂) T htime
  refine ⟨(stageIndex ε Δ L₂ + 1) * ∑ j, K j, ?_⟩
  intro Seed _ ν _ A
  obtain ⟨hspectral, hterminal⟩ := hbudget Seed ν A
  exact S.hard_function_of_terminal_budgets hε hL₁ hL₂ hregime hmass K ν A T hspectral hterminal

/-- The main randomized first-order lower bound, with the dimension
quantified before the seed space, seed measure, and algorithm. -/
theorem main_lower_bound : MainLowerBound := by
  refine ⟨parameterConstant, massThreshold, parameterConstant_pos, massThreshold_pos, ?_⟩
  intro ε Δ L₁ L₂ hε hΔ hL₁ hL₂ hregime hmass T hT
  exact hard_dimension_below_rate hε hΔ hL₁ hL₂ hregime hmass T hT

end RandomizedFO2003.Model
