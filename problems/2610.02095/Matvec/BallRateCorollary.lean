import Matvec.RateCorollary
import Matvec.BallDimensionAlgorithm

/-! The ball accuracy-rate corollary in every larger pair of dimensions. -/

namespace Matvec
open MeasureTheory
noncomputable section

theorem GameQueryLowerBound.ball_extension {m n M N : ℕ} {ε bound : ℝ}
    (h : GameQueryLowerBound .ballSimplex m n ε bound)
    (hm : 0 < m) (hn : 0 < n) (hM : m ≤ M) (hN : n ≤ N) :
    GameQueryLowerBound .ballSimplex M N ε bound := by
  intro T Seed inst alg μ hμ hsolve
  letI := hμ
  obtain ⟨core, hcore⟩ := DimensionExtension.exists_ball_core_algorithm hm hn hM hN alg μ ε hsolve
  exact h T Seed core μ hμ hcore

/-- Full ball case of `cor:rates`, including all larger row and column
dimensions. The sequence lower bound is the only explicit premise. -/
theorem ball_rates_of_main_sequences (hmain : MainSequenceLowerBounds) :
    ∃ C a b ε₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ N : ℕ, 0 < N ∧
        a * ε ^ (-(2 / 3 : ℝ)) ≤ N ∧ (N : ℝ) ≤ b * ε ^ (-(2 / 3 : ℝ)) ∧
        ∀ m n : ℕ, 4 * N ≤ m → 2 * N + 1 ≤ n →
          GameQueryLowerBound .ballSimplex m n ε (C * ballPrecisionRate ε) := by
  obtain ⟨C, a, b, ε₀, hC, ha, hb, hε₀, hcores⟩ := ball_core_rates_of_main_sequences hmain
  refine ⟨C, a, b, ε₀, hC, ha, hb, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨N, hN, hlo, hhi, hlower⟩ := hcores ε hε hsmall
  refine ⟨N, hN, hlo, hhi, ?_⟩
  intro m n hm hn
  exact hlower.ball_extension (by omega) (by omega) hm hn

/-- `cor:rates`, stated with explicit positive universal constants, every
sufficiently small positive accuracy, and every larger pair of dimensions. -/
def HighDimensionalRates : Prop :=
  (∃ C a b ε₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ N : ℕ, 0 < N ∧
      a * ε ^ (-(2 / 3 : ℝ)) ≤ N ∧ (N : ℝ) ≤ b * ε ^ (-(2 / 3 : ℝ)) ∧
      ∀ m n : ℕ, 4 * N ≤ m → 2 * N + 1 ≤ n →
        GameQueryLowerBound .ballSimplex m n ε (C * ballPrecisionRate ε)) ∧
  (∃ C a b ε₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ N : ℕ, 0 < N ∧
      a * simplexCoreRate ε ≤ N ∧ (N : ℝ) ≤ b * simplexCoreRate ε ∧
      ∀ m n : ℕ, 4 * N ≤ m → 4 * N ≤ n →
        GameQueryLowerBound .simplexSimplex m n ε (C * simplexPrecisionRate ε))

theorem main_sequences_imply_high_dimensional_rates
    (hmain : MainSequenceLowerBounds) : HighDimensionalRates :=
  ⟨ball_rates_of_main_sequences hmain, simplex_rates_of_main_sequences hmain⟩

end
end Matvec
