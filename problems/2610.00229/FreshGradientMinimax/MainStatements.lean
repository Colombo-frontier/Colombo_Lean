import FreshGradientMinimax.Minimax

/-! Exact proposition definitions for the main claims. Their proofs are
in MainTheorem34, NoiseFreeEndpoint and UnlocalizedLower. This file only
defines the statements; the named theorem modules establish them. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def logarithmicEnvelope (p : Parameters) : ℝ :=
  1 + Real.log (2 + p.κ) + Real.log (2 + p.L * p.gap / p.ε ^ 2) +
    Real.log (2 + p.κ ^ 2 * p.σ ^ 2 / p.ε ^ 2)

def upperRate (p : Parameters) : ℝ :=
  p.deterministic + p.stochastic + p.testing + Real.sqrt p.κ *
    Real.log (2 + p.κ ^ 2 * p.G ^ 2 / p.ε ^ 2 + p.κ ^ 2 * p.L * p.gap / p.ε ^ 2)

/-- Theorem 3.4 lower bound, expressed for every sufficient fixed integer budget.
The universal constants are outside the quantifier over all problem parameters. -/
def LocalizedLowerStatement : Prop :=
  ∃ c C₀ κ₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < κ₀ ∧
    ∀ p : Parameters, κ₀ ≤ p.κ → C₀ * p.ε ^ 2 ≤ p.L * p.gap →
      ∀ N : ℕ, BudgetSuffices p (some p.G) N → c * p.rate ≤ N

/-- Theorem G.1 / Theorem 3.4 upper bound with its displayed G-independent
logarithmic prefactor, including the actual existence of an algorithm. -/
def LocalizedUpperStatement : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ p : Parameters, p.ε ^ 2 ≤ p.L * p.gap →
    ∃ N : ℕ, BudgetSuffices p (some p.G) N ∧
      (N : ℝ) ≤ C₁ * logarithmicEnvelope p ^ 10 * upperRate p

def MainTheorem34Statement : Prop := LocalizedLowerStatement ∧ LocalizedUpperStatement

/-- Theorem 3.6, with no dual localization constraint in the instance class. -/
def MainTheorem36Statement : Prop :=
  ∀ p : Parameters, 4 * p.μ ≤ p.L → 80 * p.ε ^ 2 / p.L ≤ p.gap →
    unlocalizedComplexity p = ⊤

end FreshGradientMinimax
