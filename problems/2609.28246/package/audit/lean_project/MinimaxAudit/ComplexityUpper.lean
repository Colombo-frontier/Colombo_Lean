import MinimaxAudit.ComplexityModel
import MinimaxAudit.BorelScalarUpper
import MinimaxAudit.BudgetExecution
import MinimaxAudit.ComplexityArithmetic

/-! The constructed Borel scalar solver supplies a single finite budget
uniform over every public domain and finite dimension. Taking its infimum
then yields the real-valued upper bound with its exact logarithmic power. -/
namespace MinimaxAudit
open Set MeasureTheory
open scoped ENNReal
noncomputable section

def criterionResidualTolerance (E : OracleErrorCriterion) (D eps : ℝ) : ℝ :=
  match E with
  | .tangent => eps
  | .gap => eps / D

def criterionUpperCost (E : OracleErrorCriterion) (p : ℕ) (C L D eps : ℝ) : ℝ :=
  C * (1 + (criterionRatio E p L D eps) ^ (2 / (3 * (p : ℝ) - 1))) *
    (1 + Real.log (3 + criterionRatio E p L D eps)) ^ (6 * (p-1))

theorem criterionUpperCost_nonneg (E : OracleErrorCriterion) (p : ℕ)
    {C L D eps : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hD : 0 < D) (heps : 0 < eps) :
    0 ≤ criterionUpperCost E p C L D eps := by
  have hQ : 0 < criterionRatio E p L D eps := by
    cases E <;> simp only [criterionRatio] <;> positivity
  have hlog : 0 ≤ Real.log (3 + criterionRatio E p L D eps) :=
    Real.log_nonneg (by linarith)
  unfold criterionUpperCost
  positivity

/-- A uniform natural budget is derived from the actual public cap bound,
with no objective-dependent policy selection. The floor cannot remove any
calls because the original cap is already an integer. -/
theorem global_successful_upper_budget (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : OracleErrorCriterion) (L D eps : ℝ), 0 < L → 0 < D → 0 < eps →
        DetSuccessfulBudget E p L D eps (Nat.floor (criterionUpperCost E p C L D eps)) := by
  obtain ⟨C,hC,hupper⟩ := BorelScalarUpper.uniform_evaluated_borel_scalar_upper p hp
  refine ⟨C,hC,?_⟩
  intro E L D eps hL hD heps dx dy X Y hpub
  obtain ⟨x0,hx0⟩ := hpub.primal_nonempty
  obtain ⟨y0,hy0⟩ := hpub.dual_nonempty
  let z0 := joinBlocks x0 y0
  have hz0 : z0 ∈ productDomain X Y := by simpa [z0,productDomain] using And.intro hx0 hy0
  let delta := criterionResidualTolerance E D eps
  have hdelta : 0 < delta := by cases E <;> dsimp [delta,criterionResidualTolerance] <;> positivity
  obtain ⟨N,A,hcost,hsolve,_heval⟩ := hupper dx dy L D X Y hL hD
    hpub.primal_nonempty hpub.dual_nonempty hpub.primal_compact hpub.dual_compact
    hpub.primal_convex hpub.dual_convex hpub.diameter_bound z0 hz0 delta hdelta
  have hcost' : (N : ℝ) ≤ criterionUpperCost E p C L D eps := by
    cases E
    · change (N : ℝ) ≤ ScalarUpper.scalarUpperCost p C L D eps
      exact hcost
    · change (N : ℝ) ≤ ScalarUpper.scalarGapUpperCost p C L D eps
      have h := hcost
      change (N : ℝ) ≤ ScalarUpper.scalarUpperCost p C L D (eps / D) at h
      simpa only [ScalarUpper.scalar_upper_gap_cost hD.ne'] using h
  have hNB : N ≤ Nat.floor (criterionUpperCost E p C L D eps) := Nat.le_floor hcost'
  refine ⟨A.monoBudget hNB,?_⟩
  intro phi hadm
  rw [borel_monoBudget_run]
  cases E
  · exact (hsolve phi hadm).1
  · have hres := (hsolve phi hadm).1
    have hfeas := Deterministic.runScalarPolicy_feasible A.policy (exactScalarJet p phi) N []
    have hgap := admissible_gap_le_diameter_tangent hadm hfeas
    change criterionValue .gap X Y phi _ ≤ eps
    change _ ≤ eps / D at hres
    have hmul := mul_le_mul_of_nonneg_left hres hD.le
    have heq : D * (eps / D) = eps := by field_simp
    exact hgap.trans (heq ▸ hmul)

/-- Actual global deterministic complexity upper bound, with infinity and
all public domains handled by the successful-budget infimum definition. -/
theorem detOracleComplexity_upper (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : OracleErrorCriterion) (L D eps : ℝ), 0 < L → 0 < D → 0 < eps →
        (detOracleComplexity E p L D eps : ℝ≥0∞) ≤
          ENNReal.ofReal (criterionUpperCost E p C L D eps) := by
  obtain ⟨C,hC,hbudget⟩ := global_successful_upper_budget p hp
  refine ⟨C,hC,?_⟩
  intro E L D eps hL hD heps
  have h := detOracleComplexity_le_budget (hbudget E L D eps hL hD heps)
  calc
    (detOracleComplexity E p L D eps : ℝ≥0∞) ≤
        ((Nat.floor (criterionUpperCost E p C L D eps) : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_mono h
    _ = ENNReal.ofReal ((Nat.floor (criterionUpperCost E p C L D eps) : ℕ) : ℝ) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Nat.floor_le (criterionUpperCost_nonneg E p hC.le hL hD heps))

/-- Absorb the additive budget term once the requested dimensionless ratio
is at least one; the exact exponent/logarithm powers are unchanged. -/
theorem criterionUpperCost_asymptotic (E : OracleErrorCriterion) {p : ℕ} (hp : 2 ≤ p)
    {C L D eps : ℝ} (hC : 0 ≤ C) (hQ : 1 ≤ criterionRatio E p L D eps) :
    criterionUpperCost E p C L D eps ≤
      (2*C) * (criterionRatio E p L D eps) ^ (2 / (3 * (p : ℝ)-1)) *
        (1 + Real.log (3 + criterionRatio E p L D eps)) ^ (6 * (p-1)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < 3 * (p : ℝ)-1 := by linarith
  have halpha : 0 ≤ 2 / (3 * (p : ℝ)-1) := (div_pos (by norm_num) hden).le
  have hlog : 0 ≤ Real.log (3 + criterionRatio E p L D eps) := Real.log_nonneg (by linarith)
  exact upper_budget_additive_absorption halpha hQ hC (by positivity)
end
end MinimaxAudit
