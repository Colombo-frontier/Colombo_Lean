import Matvec.RateInversion
import Matvec.DimensionAlgorithm

/-!
# Accuracy-rate corollaries for actual randomized game algorithms

The sequence theorem is an explicit hypothesis of these transfer lemmas.
The integer core choice, every-small-accuracy quantifier, powers of logarithms,
and larger simplex dimensions are proved here.
-/

namespace Matvec
open MeasureTheory
noncomputable section

def GameQueryLowerBound (g : Geometry) (m n : ℕ) (ε bound : ℝ) : Prop :=
  ∀ (T : ℕ) (Seed : Type) [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (μ : Measure Seed), IsProbabilityMeasure μ →
      Solves alg μ g ε → bound ≤ T

theorem GameQueryLowerBound.simplex_extension {m n M N : ℕ} {ε bound : ℝ}
    (h : GameQueryLowerBound .simplexSimplex m n ε bound)
    (hm : 0 < m) (hn : 0 < n) (hM : m ≤ M) (hN : n ≤ N) :
    GameQueryLowerBound .simplexSimplex M N ε bound := by
  intro T Seed inst alg μ hμ hsolve
  letI := hμ
  obtain ⟨core, hcore⟩ := DimensionExtension.exists_core_algorithm hm hn hM hN alg μ ε hsolve
  exact h T Seed core μ hμ hcore

/-- Ball rate at the actual core dimensions, for every sufficiently small
positive ε. The core size is bounded on both sides by constants times ε^(-2/3). -/
theorem ball_core_rates_of_main_sequences (hmain : MainSequenceLowerBounds) :
    ∃ C a b ε₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ N : ℕ, 0 < N ∧
        a * ε ^ (-(2 / 3 : ℝ)) ≤ N ∧ (N : ℝ) ≤ b * ε ^ (-(2 / 3 : ℝ)) ∧
        GameQueryLowerBound .ballSimplex (4 * N) (2 * N + 1) ε (C * ballPrecisionRate ε) := by
  obtain ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, N₀, hseq⟩ := hmain
  obtain ⟨ε₀, hε₀, hcores⟩ := ball_rate_core_small c₀ hc₀ N₀
  refine ⟨c₂ * (c₀ ^ (2 / 3 : ℝ) / 16), c₀ ^ (2 / 3 : ℝ) / 2,
    c₀ ^ (2 / 3 : ℝ), ε₀, by positivity, by positivity, by positivity, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨N, hN₀, hN, hlo, hhi, hacc, hrate⟩ := hcores ε hε hsmall
  refine ⟨N, hN, hlo, hhi, ?_⟩
  intro T Seed inst alg μ hμ hsolve
  letI := hμ
  have hs := (hseq N hN₀).1 T Seed alg μ hμ (hsolve.mono hacc)
  have hr := mul_le_mul_of_nonneg_left hrate hc₂.le
  calc
    _ = c₂ * ((c₀ ^ (2 / 3 : ℝ) / 16) * ballPrecisionRate ε) := by ring
    _ ≤ c₂ * sourceRate N := hr
    _ ≤ T := hs

/-- Simplex rate in every pair of dimensions at least 4N. The construction
proves N=Θ(ε^(-2/3)/log(1/ε)^(1/3)) and the log^(7/3) query denominator. -/
theorem simplex_rates_of_main_sequences (hmain : MainSequenceLowerBounds) :
    ∃ C a b ε₀ : ℝ, 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ N : ℕ, 0 < N ∧
        a * simplexCoreRate ε ≤ N ∧ (N : ℝ) ≤ b * simplexCoreRate ε ∧
        ∀ m n : ℕ, 4 * N ≤ m → 4 * N ≤ n →
          GameQueryLowerBound .simplexSimplex m n ε (C * simplexPrecisionRate ε) := by
  obtain ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, N₀, hseq⟩ := hmain
  obtain ⟨ε₀, hε₀, hcores⟩ := simplex_rate_core_small c₁ hc₁ N₀
  refine ⟨c₂ * ((c₁ / 2) ^ (2 / 3 : ℝ) / 16), (c₁ / 2) ^ (2 / 3 : ℝ) / 2,
    (c₁ / 2) ^ (2 / 3 : ℝ), ε₀, by positivity, by positivity, by positivity, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨N, hN₀, hN, hlo, hhi, hacc, hrate⟩ := hcores ε hε hsmall
  refine ⟨N, hN, hlo, hhi, ?_⟩
  intro m n hm hn
  apply GameQueryLowerBound.simplex_extension ?_ (by omega) (by omega) hm hn
  intro T Seed inst alg μ hμ hsolve
  letI := hμ
  have hs := (hseq N hN₀).2 T Seed alg μ hμ (hsolve.mono hacc)
  have hr := mul_le_mul_of_nonneg_left hrate hc₂.le
  calc
    _ = c₂ * (((c₁ / 2) ^ (2 / 3 : ℝ) / 16) * simplexPrecisionRate ε) := by ring
    _ ≤ c₂ * sourceRate N := hr
    _ ≤ T := hs

end
end Matvec
