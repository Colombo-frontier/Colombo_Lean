import Matvec.OrdinarySourceRate
import Matvec.SourceCoordinates
import Matvec.SourceMatrixRepresentation
import Matvec.GameSourceSolver
import Matvec.DimensionAlgorithm
import Matvec.GameScaleArithmetic

/-! The unconditional main sequence lower bounds for actual randomized
matrix-game algorithms. The dyadic Walsh construction is transported to
every sufficiently large core size with its query count unchanged. -/
namespace Matvec
open MeasureTheory MeasurableSimulation GameSourceSolver RandomOrthogonal
noncomputable section

theorem main_sequence_lower_bounds : MainSequenceLowerBounds := by
  obtain ⟨κ, c, hκ, hc, N₀, hsource⟩ := ordinary_source_solver_rate_lower_bound.{0, 0}
  let K := max κ 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right κ 1)
  have hκK : κ ≤ K := le_max_left _ _
  have hK1 : 1 ≤ K := le_max_right _ _
  refine ⟨1 / (1024 * K), 1 / (32 * K), c / 4, by positivity,
    by positivity, by positivity, 2 * max N₀ 1, ?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  have hNN₀ : N₀ ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  constructor
  · intro T Seed instSeed alg μ hμ hsolve
    letI := hμ
    have hKN : 1 ≤ K * N := by nlinarith
    have hacc : (1 / (1024 * K)) / (N : ℝ) ^ (3 / 2 : ℝ) ≤
        ballAccuracy (2 * N) (K * N) :=
      ball_accuracy_threshold (by omega) hNpos le_rfl (by positivity) hK le_rfl
    have hs := hsolve.mono hacc
    let base := ballSourcePolicy alg (ballRowEquiv N) (ballColumnEquiv N) (K * N)
    have hlower := hsource N hNN₀ (EuclideanSpace ℝ (Fin (2 * N)))
      (dilationFinIsometry N) (2 * T) Seed μ hμ base
      (source_policy_success_of_matrix base μ (κ * N) (by
        intro A hsym hexp hnorm r
        exact ballSourcePolicy_success alg μ (ballRowEquiv N) (ballColumnEquiv N)
          (K * N) hKN (by omega) hs A hsym hexp
          (hnorm.trans (mul_le_mul_of_nonneg_right hκK (by positivity))) r))
    have hr := (sourceRate_pos hNpos).le
    push_cast at hlower
    nlinarith
  · intro T Seed instSeed alg μ hμ hsolve
    letI := hμ
    obtain ⟨k, hMpos, hMN, hNM⟩ := SimplexNormalization.exists_dyadic_core N hNpos
    have hM₀ : N₀ ≤ 2 ^ k := by omega
    have hMR : (1 : ℝ) ≤ (2 ^ k : ℕ) := by exact_mod_cast hMpos
    have hKM : 1 ≤ K * (2 ^ k : ℕ) := by nlinarith
    obtain ⟨core, hcore⟩ := DimensionExtension.exists_core_algorithm
      (by omega : 0 < 4 * 2 ^ k) (by omega : 0 < 4 * 2 ^ k)
      (by omega : 4 * 2 ^ k ≤ 4 * N) (by omega : 4 * 2 ^ k ≤ 4 * N)
      alg μ _ hsolve
    have hacc₁ := simplex_accuracy_antitone hMpos hMN
      (by positivity : 0 ≤ 1 / (32 * K))
    have hacc₂ : (1 / (32 * K)) /
        (((2 ^ k : ℕ) : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log ((2 ^ k : ℕ) + 2))) ≤
        simplexAccuracy (k + 1) (K * (2 ^ k : ℕ)) := by
      have h := simplex_accuracy_threshold (d := 2 ^ (k + 1)) (N := 2 ^ k)
        (by positivity) hMpos (by rw [pow_succ]; omega)
        (κ := K * (2 ^ k : ℕ)) (by positivity) hK le_rfl
      simpa only [simplexAccuracy, SimplexNormalization.embeddingScale,
        Nat.cast_pow, Nat.cast_ofNat] using h
    have hs := hcore.mono (hacc₁.trans hacc₂)
    let base := simplexSourcePolicy core (k + 1) (simplexCubeEquiv k)
      (simplexCubeEquiv k) (K * (2 ^ k : ℕ))
    let ν := (signLaw (Cube (k + 1))).prod μ
    have hlower := hsource (2 ^ k) hM₀ (EuclideanSpace ℝ (Cube (k + 1)))
      (dilationCubeIsometry k) (2 * T) (SimplexSeed (k + 1) Seed) ν inferInstance base
      (source_policy_success_of_matrix base ν (κ * (2 ^ k : ℕ)) (by
        intro A hsym hexp hnorm r
        exact simplexSourcePolicy_success core μ (k + 1) (simplexCubeEquiv k)
          (simplexCubeEquiv k) (K * (2 ^ k : ℕ)) hKM hs A hsym hexp
          (hnorm.trans (mul_le_mul_of_nonneg_right hκK (by positivity))) r))
    have hcompare := sourceRate_core_comparison hMN hNM.le
    push_cast at hlower
    nlinarith

end
end Matvec
