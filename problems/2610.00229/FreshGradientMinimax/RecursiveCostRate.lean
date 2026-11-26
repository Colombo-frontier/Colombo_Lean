import FreshGradientMinimax.SCSCProgram

/-! Each actual recursive solve satisfies F.3's cost theorem with the
required uniform smoothness range. Summing preserves the separation
between initialization and statistical cost. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem recursiveMass_monotone {μ : ℝ} (hμ : 0 ≤ μ) : Monotone (recursiveMass μ) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij) hμ

theorem recursiveCurvature_stage_bound {ℓ μ : ℝ} (hμ : 0 < μ) (hμℓ : μ ≤ ℓ)
    {j : ℕ} (hj : j ≤ recursiveLastIndex (5 * ℓ) μ) : recursiveCurvature μ j ≤ 10 * ℓ := by
  have hℓ := hμ.trans_le hμℓ
  have hμH : μ ≤ 5 * ℓ := by linarith
  have hlast := (recursiveLastIndex_mass hμ hμH).2
  have hmono := recursiveMass_monotone hμ.le hj
  have hc := recursiveCurvature_le_mass hμ.le j
  linarith

theorem recursiveInputEnvelope_nonneg {μ δ E : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (N j : ℕ) : 0 ≤ recursiveInputEnvelope μ δ N E j := by
  cases j with
  | zero => exact hE
  | succ j => exact mul_nonneg (by norm_num) (recursiveAccuracy_pos hμ hδ N j).le

theorem recursiveStageWork_rate {ℓ α σ μ δ E : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hμ : 0 < μ) (hμℓ : μ ≤ ℓ)
    (hδ : 0 < δ) (hE : 0 ≤ E) {j : ℕ} (hj : j ≤ recursiveLastIndex (5 * ℓ) μ) :
    recursiveStageWork ℓ α σ μ δ (recursiveLastIndex (5 * ℓ) μ) E j ≤
      10 ^ 70 * valueLogFactor ℓ σ (recursiveMass μ j)
        (recursiveAccuracy μ δ (recursiveLastIndex (5 * ℓ) μ) j) ^ 3 *
      (Real.sqrt ((5 * ℓ + recursiveCurvature μ j) / recursiveMass μ j) *
        Real.log (2 + recursiveInputEnvelope μ δ (recursiveLastIndex (5 * ℓ) μ) E j /
          recursiveAccuracy μ δ (recursiveLastIndex (5 * ℓ) μ) j) +
        σ ^ 2 / (recursiveMass μ j * recursiveAccuracy μ δ (recursiveLastIndex (5 * ℓ) μ) j)) := by
  have hc := recursiveCurvature_stage_bound hμ hμℓ hj
  have ha := recursiveCurvature_nonneg hμ j
  unfold recursiveStageWork
  rw [recursiveMass_add_curvature]
  apply valueSolverWork_rate hℓ hα hfast (recursiveMass_pos hμ j)
  · rw [← recursiveMass_add_curvature]; linarith
  · linarith
  · exact recursiveAccuracy_pos hμ hδ _ j
  · exact recursiveInputEnvelope_nonneg hμ hδ hE _ j

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem recursiveSolverProgram_calls_sum_rate (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {δ E : ℝ} (hδ : 0 < δ) (hE : 0 ≤ E)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂(recursiveSolverProgram dx dy ℓ α σ μ δ (recursiveLastIndex (5 * ℓ) μ) E).originalKernel O.kernel ∘ₘ ν) ≤
      ∑ j ∈ Finset.range (recursiveLastIndex (5 * ℓ) μ + 1),
        10 ^ 70 * valueLogFactor ℓ σ (recursiveMass μ j)
          (recursiveAccuracy μ δ (recursiveLastIndex (5 * ℓ) μ) j) ^ 3 *
        (Real.sqrt ((5 * ℓ + recursiveCurvature μ j) / recursiveMass μ j) *
          Real.log (2 + recursiveInputEnvelope μ δ (recursiveLastIndex (5 * ℓ) μ) E j /
            recursiveAccuracy μ δ (recursiveLastIndex (5 * ℓ) μ) j) +
          σ ^ 2 / (recursiveMass μ j * recursiveAccuracy μ δ (recursiveLastIndex (5 * ℓ) μ) j)) := by
  rw [(S.recursiveSolverProgram_mean_calls O δ _ E ν).2]
  apply Finset.sum_le_sum
  intro j hj
  exact recursiveStageWork_rate S.L_pos S.α_pos hfast S.μ_pos S.μ_le_L hδ hE (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

end SCObjective
end FreshGradientMinimax
