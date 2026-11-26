import FullJet.ExpectedLowerBound
import FullJet.ExpectedUpperMethod

open scoped ENNReal

namespace FullJet

/-- Matching minimax expected query complexity with the expected-gradient
criterion, for actual stopping algorithms in every finite dimension.
No confidence logarithm is needed for the certified restart upper bound. -/
theorem main_expected_complexity_theorem (p : ℕ) (hp : 2 ≤ p) :
    ∃ (c C : ℝ) (n₀ : ℕ), 0 < c ∧ 0 < C ∧ 0 < n₀ ∧ ∀ n, n₀ ≤ n →
      ∀ (Δ L ε : ℝ), 0 < Δ → 0 < L → 0 < ε →
        ENNReal.ofReal (c * ((n : ℝ) + (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) *
          (Δ * L ^ (1 / (p : ℝ)) * ε ^ (-((p : ℝ) + 1) / p)))) ≤
            expectedOracleComplexity n p Δ L ε ∧
        expectedOracleComplexity n p Δ L ε ≤
          ENNReal.ofReal (C * ((n : ℝ) + (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) *
            (Δ * L ^ (1 / (p : ℝ)) * ε ^ (-((p : ℝ) + 1) / p)))) := by
  refine ⟨expectedLowerConstant p, expectedUpperConstant p, expectedSampleThreshold p,
    expectedLowerConstant_pos p, expectedUpperConstant_pos p, expectedSampleThreshold_pos p, ?_⟩
  intro n hn Δ L ε hΔ hL hε
  have hnpos : 0 < n := (expectedSampleThreshold_pos p).trans_le hn
  constructor
  · simpa only [fullRate, accuracyRate, accuracyWork_eq_manuscript p (by omega)] using
      expectedOracleComplexity_lower p n hp hn Δ L ε hΔ hL hε
  · simpa only [fullRate, accuracyRate, accuracyWork_eq_manuscript p (by omega)] using
      expectedOracleComplexity_upper p n hp hnpos Δ L ε hΔ hL hε

end FullJet
