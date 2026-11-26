import NCConcave16991.BaselineProblem
import NCConcave16991.BaselineCounting
import NCConcave16991.OracleIndistinguishability
import NCConcave16991.TheoremStatements

/-!
# An unrestricted randomized hidden-component lower bound

The finite hard family consists of actual individually smooth, lower-bounded
quadratic Problems. Policies may use arbitrary private probability spaces,
query locations, complete histories, early stopping, and unqueried outputs.
-/

open Set MeasureTheory
open scoped ENNReal

namespace NCConcave16991.BaselineProblem

noncomputable section

theorem hidden_component_lower (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p) :
    LowerBudgetBound p .individual ((p.n : ℝ) / 3) := by
  intro T hvalid
  have hgap : (2 * p.epsilon) ^ 2 / (2 * p.L) ≤ p.gap := by
    have hh := (le_div_iff₀ (sq_pos_of_pos p.epsilon_pos)).mp hA
    apply (div_le_iff₀ (mul_pos (by norm_num) p.L_pos)).2
    nlinarith only [hh]
  have hgapNeg : (- (2 * p.epsilon)) ^ 2 / (2 * p.L) ≤ p.gap := by
    simpa only [neg_sq] using hgap
  obtain ⟨A, hApol⟩ := hvalid 1 0 (dualDomain p) 0
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  let plus := fun j : Fin p.n ↦ model p (2 * p.epsilon) j hgap
  let minus := fun j : Fin p.n ↦ model p (-(2 * p.epsilon)) j hgapNeg
  let EA := fun j : Fin p.n ↦ {seed : A.Seed | StationaryOutput (plus j)
    (OraclePolicy.run (dualDomain p) A.policy (oracleResponse (plus j)) seed T).1}
  let EB := fun j : Fin p.n ↦ {seed : A.Seed | StationaryOutput (minus j)
    (OraclePolicy.run (dualDomain p) A.policy (oracleResponse (minus j)) seed T).1}
  have hplus (j : Fin p.n) : MeasurableSet (EA j) ∧ (2/3 : ℝ≥0∞) ≤ A.law (EA j) := by
    exact hApol (plus j) rfl (model_individualSmooth p _ j hgap)
  have hminus (j : Fin p.n) : MeasurableSet (EB j) ∧ (2/3 : ℝ≥0∞) ≤ A.law (EB j) := by
    exact hApol (minus j) rfl (model_individualSmooth p _ j hgapNeg)
  let visited := fun seed : A.Seed ↦ OraclePolicy.componentSupport (dualDomain p)
    (OraclePolicy.run (dualDomain p) A.policy (baseOracle p) seed T).2
  apply BaselineCounting.randomized_budget_lower A.law EA EB
    (fun j ↦ (hplus j).1) (fun j ↦ (hminus j).1)
    (fun j ↦ (hplus j).2) (fun j ↦ (hminus j).2) visited
  · intro seed
    exact OraclePolicy.run_componentSupport_card (dualDomain p) A.policy (baseOracle p) seed T
  · intro seed j hj
    have hp := OraclePolicy.run_eq_of_hidden_component (dualDomain p) A.policy
      (baseOracle p) (oracleResponse (plus j)) seed j
      (fun q hq ↦ oracle_agrees p _ j hgap q hq) T hj
    have hm := OraclePolicy.run_eq_of_hidden_component (dualDomain p) A.policy
      (baseOracle p) (oracleResponse (minus j)) seed j
      (fun q hq ↦ oracle_agrees p _ j hgapNeg q hq) T hj
    rintro ⟨hsplus, hsminus⟩
    change StationaryOutput (plus j)
      (OraclePolicy.run (dualDomain p) A.policy (oracleResponse (plus j)) seed T).1 at hsplus
    change StationaryOutput (minus j)
      (OraclePolicy.run (dualDomain p) A.policy (oracleResponse (minus j)) seed T).1 at hsminus
    rw [hp] at hsplus
    rw [hm] at hsminus
    exact BaselineHilbert.opposite_stationary_disjoint p.L_pos direction direction_norm _
      (by linarith [p.epsilon_pos])
      (stationary_norm p _ j hgap _ hsplus) (stationary_norm p _ j hgapNeg _ hsminus)

theorem hidden_component_lower_averaged (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p) :
    LowerBudgetBound p .averaged ((p.n : ℝ) / 3) :=
  lowerBudget_averaged_of_individual (hidden_component_lower p hA)

theorem oracleComplexity_lower (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p)
    (mode : SmoothnessClass) :
    ENNReal.ofReal ((p.n : ℝ) / 3) ≤ oracleComplexity p mode := by
  have hlower : LowerBudgetBound p mode ((p.n : ℝ) / 3) := by
    cases mode with
    | individual => exact hidden_component_lower p hA
    | averaged => exact hidden_component_lower_averaged p hA
  unfold oracleComplexity
  apply le_iInf
  intro budget
  have hh := ENNReal.ofReal_le_ofReal (hlower budget.val budget.property)
  simpa only [ENNReal.ofReal_natCast] using hh

end

end NCConcave16991.BaselineProblem
