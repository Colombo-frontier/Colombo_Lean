import FullJet.UpperRate
import FullJet.ConfidenceRounds

namespace FullJet

/-- The matching upper rate, with its confidence logarithm made explicit.
The budget is supplied by the constructed, validated oracle method. -/
theorem oracleComplexity_matching_upper (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (Δ L ε δ : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    oracleComplexity n p Δ L ε δ ≤
      ENNReal.ofReal (mainUpperConstant p * confidenceFactor δ * fullRate p n Δ L ε) := by
  have h := oracleComplexity_verified_upper p n hp hn Δ L ε δ n 1 (confidenceRounds δ)
    hΔ hL hε hn (by omega) (confidenceRounds_failure_le δ hδ)
  have hb := verifiedQueryBudget_le p n (by omega) hn Δ L ε (confidenceRounds δ) hΔ hL hε
  have hr : 0 ≤ fullRate p n Δ L ε := by
    exact add_nonneg (Nat.cast_nonneg n) (accuracyRate_nonneg p n Δ L ε hΔ hL hε)
  have hc := mul_le_mul_of_nonneg_right (confidenceRounds_le δ hδ hδ1)
    (mul_nonneg (mainUpperConstant_pos p).le hr)
  have hb' : (verifiedQueryBudget p n Δ L ε n 1 (confidenceRounds δ) : ℝ) ≤
      mainUpperConstant p * confidenceFactor δ * fullRate p n Δ L ε := by
    calc
      _ ≤ (confidenceRounds δ : ℝ) * mainUpperConstant p * fullRate p n Δ L ε := hb
      _ ≤ confidenceFactor δ * (mainUpperConstant p * fullRate p n Δ L ε) := by
        simpa only [mul_assoc] using hc
      _ = _ := by ring
  exact h.trans (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb')

/-- Both sides of the manuscript's principal complexity theorem. The upper
bound displays the logarithmic confidence factor instead of hiding it in
asymptotic notation; all component replies and validation calls are counted. -/
theorem main_complexity_theorem (p : ℕ) (hp : 2 ≤ p) :
    ∃ (c C : ℝ) (n₀ : ℕ) (δ₀ : ℝ), 0 < c ∧ 0 < C ∧ 0 < n₀ ∧ 0 < δ₀ ∧ δ₀ < 1 / 2 ∧
      ∀ (n : ℕ), n₀ ≤ n → ∀ (Δ L ε δ : ℝ), 0 < Δ → 0 < L → 0 < ε → 0 < δ → δ < δ₀ →
        let rate := (n : ℝ) + (n : ℝ) ^ (1 - 1 / (2 * (p : ℝ))) *
          (Δ * L ^ (1 / (p : ℝ)) * ε ^ (-((p : ℝ) + 1) / p))
        ENNReal.ofReal (c * rate) ≤ oracleComplexity n p Δ L ε δ ∧
          oracleComplexity n p Δ L ε δ ≤
            ENNReal.ofReal (C * (1 + Real.log (1 / δ) / Real.log 4) * rate) := by
  obtain ⟨c, n₀, δ₀, hc, hn₀, hδ₀, hδhalf, hlower⟩ := main_complexity_lower_bound p hp
  refine ⟨c, mainUpperConstant p, n₀, δ₀, hc, mainUpperConstant_pos p, hn₀, hδ₀, hδhalf, ?_⟩
  intro n hn Δ L ε δ hΔ hL hε hδ hδlt
  constructor
  · exact hlower n hn Δ L ε δ hΔ hL hε hδ hδlt
  · have hupper := oracleComplexity_matching_upper p n hp (Nat.lt_of_lt_of_le hn₀ hn)
      Δ L ε δ hΔ hL hε hδ (by linarith)
    simpa only [confidenceFactor_eq, fullRate, accuracyRate,
      accuracyWork_eq_manuscript p (by omega)] using hupper

end FullJet
