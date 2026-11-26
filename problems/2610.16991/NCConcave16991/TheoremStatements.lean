import NCConcave16991.Problem
import NCConcave16991.Rates
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Explicit main theorem specifications

The declarations ending in `Specification` below define the exact propositions
over the actual mathematical problem and randomized policies. Their proofs are
provided in `UpperTheorem`, `LowerTheorem`, and `MainTheorem`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace NCConcave16991

noncomputable section

def dimensionlessA (p : ProblemParameters) : ℝ := p.L * p.gap / p.epsilon ^ 2
def dimensionlessB (p : ProblemParameters) : ℝ := p.L * p.diameter / p.epsilon
def complexityLog (p : ProblemParameters) : ℝ :=
  Real.log (2 + (p.n : ℝ) + dimensionlessA p + dimensionlessB p)
def fullRate (p : ProblemParameters) : ℝ :=
  (p.n : ℝ) + dimensionlessA p * rate (p.n : ℝ) (dimensionlessB p)

theorem dimensionlessA_pos (p : ProblemParameters) : 0 < dimensionlessA p := by
  exact div_pos (mul_pos p.L_pos p.gap_pos) (sq_pos_of_pos p.epsilon_pos)

theorem dimensionlessB_nonneg (p : ProblemParameters) : 0 ≤ dimensionlessB p := by
  exact div_nonneg (mul_nonneg p.L_pos.le p.diameter_nonneg) p.epsilon_pos.le

/-- An upper bound means there really is a finite fixed-budget algorithm. -/
def UpperBudgetBound (p : ProblemParameters) (mode : SmoothnessClass) (bound : ℝ) : Prop :=
  ∃ budget : ℕ, ValidBudget p mode budget ∧ (budget : ℝ) ≤ bound

/-- A lower bound quantifies over all algorithms valid uniformly over the class. -/
def LowerBudgetBound (p : ProblemParameters) (mode : SmoothnessClass) (bound : ℝ) : Prop :=
  ∀ budget : ℕ, ValidBudget p mode budget → bound ≤ (budget : ℝ)

theorem lowerBudget_averaged_of_individual {p : ProblemParameters} {b : ℝ}
    (h : LowerBudgetBound p .individual b) : LowerBudgetBound p .averaged b := by
  intro budget hbudget
  exact h budget (validBudget_individual_of_averaged hbudget)

theorem upperBudget_individual_of_averaged {p : ProblemParameters} {b : ℝ}
    (h : UpperBudgetBound p .averaged b) : UpperBudgetBound p .individual b := by
  obtain ⟨budget, hbudget, hb⟩ := h
  exact ⟨budget, validBudget_individual_of_averaged hbudget, hb⟩

/-- The minimax budget is infinite if there is no finite successful budget. -/
def oracleComplexity (p : ProblemParameters) (mode : SmoothnessClass) : ℝ≥0∞ :=
  ⨅ budget : {T : ℕ // ValidBudget p mode T}, (budget.val : ℝ≥0∞)

theorem oracleComplexity_le_of_valid {p : ProblemParameters} {mode : SmoothnessClass}
    {budget : ℕ} (h : ValidBudget p mode budget) :
    oracleComplexity p mode ≤ (budget : ℝ≥0∞) :=
  iInf_le_of_le ⟨budget, h⟩ le_rfl

/-- The class inclusion gives the middle inequality of Theorem 3.1. -/
theorem individualComplexity_le_averaged (p : ProblemParameters) :
    oracleComplexity p .individual ≤ oracleComplexity p .averaged := by
  apply le_iInf
  intro budget
  exact oracleComplexity_le_of_valid (validBudget_individual_of_averaged budget.property)

/-- Equation (9) of Theorem 3.1, with possibly infinite minimax complexity. -/
def Theorem31GlobalSpecification : Prop :=
  ∃ Astar c C : ℝ, 0 < Astar ∧ 0 < c ∧ 0 < C ∧
    ∀ p : ProblemParameters, Astar ≤ dimensionlessA p →
      ENNReal.ofReal (c * fullRate p) ≤ oracleComplexity p .individual ∧
      oracleComplexity p .individual ≤ oracleComplexity p .averaged ∧
      oracleComplexity p .averaged ≤ ENNReal.ofReal (C * fullRate p * complexityLog p)

/-- The sharper piecewise part of Theorem 3.1. The first two upper bounds
have no logarithmic loss, and both classes are covered. -/
def Theorem31PiecewiseSpecification : Prop :=
  ∃ Astar c C : ℝ, 0 < Astar ∧ 0 < c ∧ 0 < C ∧
    ∀ (p : ProblemParameters) (mode : SmoothnessClass),
      Astar ≤ dimensionlessA p →
      (dimensionlessB p ≤ (p.n : ℝ) ^ (1 / 6 : ℝ) →
        let R := (p.n : ℝ) + dimensionlessA p *
          ((p.n : ℝ) ^ (1 / 2 : ℝ) * clippedDiameter (dimensionlessB p))
        LowerBudgetBound p mode (c * R) ∧ UpperBudgetBound p mode (C * R)) ∧
      ((p.n : ℝ) ^ (1 / 6 : ℝ) ≤ dimensionlessB p →
        dimensionlessB p ≤ (p.n : ℝ) ^ (1 / 4 : ℝ) →
        let R := (p.n : ℝ) + dimensionlessA p * dimensionlessB p ^ 4
        LowerBudgetBound p mode (c * R) ∧ UpperBudgetBound p mode (C * R)) ∧
      ((p.n : ℝ) ^ (1 / 4 : ℝ) ≤ dimensionlessB p →
        let R := (p.n : ℝ) + dimensionlessA p *
          ((p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p)
        LowerBudgetBound p mode (c * R) ∧
          UpperBudgetBound p mode (C * R * complexityLog p))

def randomizedOutput {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter} (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (P : Problem p dx dy K) (budget : ℕ) : A.Seed → PrimalSpace dx :=
  letI : MeasurableSpace A.Seed := A.seedSpace
  fun seed => (OraclePolicy.run K A.policy (oracleResponse P) seed budget).1

def SuccessAtProbability {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter} (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (P : Problem p dx dy K) (budget : ℕ) (probability : ℝ≥0∞) : Prop :=
  letI : MeasurableSpace A.Seed := A.seedSpace
  let event := {seed | StationaryOutput P (randomizedOutput A P budget seed)}
  MeasurableSet event ∧ probability ≤ A.law event

def SquaredExpectationGuarantee {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter} (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (P : Problem p dx dy K) (budget : ℕ) : Prop :=
  letI : MeasurableSpace A.Seed := A.seedSpace
  let squaredGradient := fun seed =>
    ‖gradient (problemMoreauEnvelope P) (randomizedOutput A P budget seed)‖ ^ 2
  (∀ seed, DifferentiableAt ℝ (problemMoreauEnvelope P) (randomizedOutput A P budget seed)) ∧
    Integrable squaredGradient A.law ∧
      (∫ seed, squaredGradient seed ∂A.law) < p.epsilon ^ 2 / 200

def ValidSquaredExpectationBudget (p : ProblemParameters) (budget : ℕ) : Prop :=
  ∀ (dx dy : ℕ) (K : KnownDualDomain dy p.diameter) (x0 : PrimalSpace dx),
    ∃ A : RandomizedPolicy K (n := p.n) (dx := dx),
      ∀ P : Problem p dx dy K, P.initialPoint = x0 → P.averagedSmooth →
        SquaredExpectationGuarantee A P budget

def ValidThreeQuartersBudget (p : ProblemParameters) (budget : ℕ) : Prop :=
  ∀ (dx dy : ℕ) (K : KnownDualDomain dy p.diameter) (x0 : PrimalSpace dx),
    ∃ A : RandomizedPolicy K (n := p.n) (dx := dx),
      ∀ P : Problem p dx dy K, P.initialPoint = x0 → P.averagedSmooth →
        SuccessAtProbability A P budget (3 / 4)

/-- The complete two algorithmic guarantees of Theorem 3.2. -/
def Theorem32Specification : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : ProblemParameters,
    (∃ budget : ℕ, ValidSquaredExpectationBudget p budget ∧
      (budget : ℝ) ≤ C * ((p.n : ℝ) + (1 + dimensionlessA p) *
        ((p.n : ℝ) ^ (1 / 2 : ℝ) * clippedDiameter (dimensionlessB p) +
          clippedDiameter (dimensionlessB p) ^ 4))) ∧
    (∃ budget : ℕ, ValidThreeQuartersBudget p budget ∧
      (budget : ℝ) ≤ C * (1 + dimensionlessA p) *
        ((p.n : ℝ) + (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p) * complexityLog p)

/-- The two unrestricted randomized lower bounds of Theorem 3.3. -/
def Theorem33Specification : Prop :=
  ∃ A0 c : ℝ, 0 < A0 ∧ 0 < c ∧
    ∀ p : ProblemParameters, A0 ≤ dimensionlessA p →
      ENNReal.ofReal (c * ((p.n : ℝ) + dimensionlessA p *
          optimizationLower (p.n : ℝ) (dimensionlessB p))) ≤ oracleComplexity p .individual ∧
      ENNReal.ofReal (c * ((p.n : ℝ) + dimensionlessA p *
          diameterLower (p.n : ℝ) (dimensionlessB p))) ≤ oracleComplexity p .individual

end

end NCConcave16991
