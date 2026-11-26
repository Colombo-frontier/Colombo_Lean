import FullJet.MainLowerBound

open MeasureTheory
open scoped ENNReal

namespace FullJet

/-- A private probability source together with an algorithm in every finite
Euclidean dimension. The probability source is part of the chosen method. -/
structure RandomizedJetMethod (n p : ℕ) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace law
  algorithm : UniformJetAlgorithm Seed n p

def RandomizedJetMethod.succeeds {n p : ℕ} (M : RandomizedJetMethod n p)
    (N : ℕ) (Δ L ε δ : ℝ) : Prop := by
  letI := M.seedSpace
  exact M.algorithm.succeeds M.law N Δ L ε δ

/-- The infimum of achievable fixed component-call budgets. It is infinite
when there is no successful method. This avoids assuming an upper bound. -/
noncomputable def oracleComplexity (n p : ℕ) (Δ L ε δ : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (N : ℕ) (M : RandomizedJetMethod n p), b = (N : ℝ≥0∞) ∧ M.succeeds N Δ L ε δ}

theorem oracleComplexity_le_of_method {n p N : ℕ} (M : RandomizedJetMethod n p)
    (Δ L ε δ : ℝ) (hM : M.succeeds N Δ L ε δ) : oracleComplexity n p Δ L ε δ ≤ N :=
  sInf_le ⟨N, M, rfl, hM⟩

theorem method_budget_lower {n p N : ℕ} (M : RandomizedJetMethod n p)
    (hp : 2 ≤ p) (hn : largeSampleThreshold ≤ n)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : δ < 1 / 4)
    (hM : M.succeeds N Δ L ε δ) : mainLowerConstant p * fullRate p n Δ L ε ≤ (N : ℝ) := by
  letI := M.seedSpace
  letI := M.probability
  exact main_lower_bound_for_algorithm M.law M.algorithm hp hn Δ L ε δ hΔ hL hε hδ hM

theorem oracleComplexity_lower {n p : ℕ} (hp : 2 ≤ p) (hn : largeSampleThreshold ≤ n)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : δ < 1 / 4) :
    ENNReal.ofReal (mainLowerConstant p * fullRate p n Δ L ε) ≤ oracleComplexity n p Δ L ε δ := by
  apply le_sInf
  rintro b ⟨N, M, rfl, hM⟩
  have h := ENNReal.ofReal_le_ofReal (method_budget_lower M hp hn Δ L ε δ hΔ hL hε hδ hM)
  simpa only [ENNReal.ofReal_natCast] using h

/-- The lower half of the manuscript's main complexity theorem, with its
original quantifier order and a fixed positive confidence threshold. The
matching upper half remains a separate algorithmic construction. -/
theorem main_complexity_lower_bound (p : ℕ) (hp : 2 ≤ p) :
    ∃ (c : ℝ) (n₀ : ℕ) (δ₀ : ℝ), 0 < c ∧ 0 < n₀ ∧ 0 < δ₀ ∧ δ₀ < 1 / 2 ∧
      ∀ (n : ℕ), n₀ ≤ n → ∀ (Δ L ε δ : ℝ), 0 < Δ → 0 < L → 0 < ε → 0 < δ → δ < δ₀ →
        ENNReal.ofReal (c * ((n : ℝ) + (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) *
          (Δ * L ^ (1 / (p : ℝ)) * ε ^ (-((p : ℝ) + 1) / p)))) ≤ oracleComplexity n p Δ L ε δ := by
  refine ⟨mainLowerConstant p, largeSampleThreshold, 1 / 4, mainLowerConstant_pos p,
    by norm_num [largeSampleThreshold, rowBudgetDivisor], by norm_num, by norm_num, ?_⟩
  intro n hn Δ L ε δ hΔ hL hε hδpos hδ
  have h := oracleComplexity_lower hp hn Δ L ε δ hΔ hL hε hδ
  simpa only [fullRate, accuracyRate, accuracyWork_eq_manuscript p (by omega)] using h

end FullJet
