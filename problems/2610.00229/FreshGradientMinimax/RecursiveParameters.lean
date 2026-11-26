import FreshGradientMinimax.EpochSchedule

/-! The dyadic curvatures, finite stage count and value accuracies of F.4.
Stage j here returns the paper's v_{j+1}, so the last index is J-1. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def recursiveMass (μ : ℝ) (j : ℕ) : ℝ := 2 ^ j * μ
def recursiveCurvature (μ : ℝ) (j : ℕ) : ℝ := recursiveMass μ j - μ
def recursiveLastIndex (H μ : ℝ) : ℕ := finalEpochIndex H μ
def recursiveAccuracy (μ δ : ℝ) (N j : ℕ) : ℝ :=
  δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2 * recursiveMass μ j)

theorem recursiveMass_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < recursiveMass μ j := by
  unfold recursiveMass
  positivity

theorem recursiveMass_succ (μ : ℝ) (j : ℕ) : recursiveMass μ (j + 1) = 2 * recursiveMass μ j := by
  simp only [recursiveMass, pow_succ]
  ring

theorem recursiveCurvature_zero (μ : ℝ) : recursiveCurvature μ 0 = 0 := by
  simp [recursiveCurvature, recursiveMass]

theorem recursiveCurvature_succ (μ : ℝ) (j : ℕ) :
    recursiveCurvature μ (j + 1) = recursiveCurvature μ j + recursiveMass μ j := by
  rw [recursiveCurvature, recursiveCurvature, recursiveMass_succ]
  ring

theorem recursiveMass_add_curvature (μ : ℝ) (j : ℕ) : μ + recursiveCurvature μ j = recursiveMass μ j := by
  unfold recursiveCurvature
  ring

theorem recursiveCurvature_sum (μ : ℝ) (j : ℕ) :
    recursiveCurvature μ j = ∑ i ∈ Finset.range j, recursiveMass μ i := by
  induction j with
  | zero => simp [recursiveCurvature_zero]
  | succ j ih => rw [recursiveCurvature_succ, Finset.sum_range_succ, ih]

theorem recursiveCurvature_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ recursiveCurvature μ j := by
  rw [recursiveCurvature_sum]
  exact Finset.sum_nonneg (fun i _ => (recursiveMass_pos hμ i).le)

theorem recursiveCurvature_le_mass {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) :
    recursiveCurvature μ j ≤ recursiveMass μ j := by unfold recursiveCurvature; linarith

theorem recursiveLastIndex_mass {μ H : ℝ} (hμ : 0 < μ) (hμH : μ ≤ H) :
    H ≤ recursiveMass μ (recursiveLastIndex H μ) ∧ recursiveMass μ (recursiveLastIndex H μ) < 2 * H := by
  obtain ⟨hl, hu⟩ := finalEpochIndex_power (E₀ := H) hμ
  rw [max_eq_left hμH] at hl hu
  constructor
  · exact (div_le_iff₀ hμ).mp hl
  · have h := mul_lt_mul_of_pos_right hu hμ
    simpa only [mul_assoc, div_mul_cancel₀ _ hμ.ne'] using h

theorem recursiveLastIndex_count {μ H : ℝ} (hμ : 0 < μ) (hμH : μ ≤ H) :
    (recursiveLastIndex H μ + 1 : ℕ) ≤ Real.log (H / μ) / Real.log 2 + 2 := by
  simpa only [recursiveLastIndex, max_eq_left hμH] using finalEpochIndex_count (E₀ := H) hμ

theorem recursiveAccuracy_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (N j : ℕ) :
    0 < recursiveAccuracy μ δ N j := by
  have := recursiveMass_pos hμ j
  unfold recursiveAccuracy
  positivity

theorem recursiveAccuracy_scaled {μ : ℝ} (hμ : 0 < μ) (δ : ℝ) (N j : ℕ) :
    recursiveMass μ j * recursiveAccuracy μ δ N j = δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2) := by
  have hm := (recursiveMass_pos hμ j).ne'
  unfold recursiveAccuracy
  field_simp
  ring

theorem recursiveAccuracy_halving (μ δ : ℝ) (N j : ℕ) :
    recursiveAccuracy μ δ N (j + 1) = recursiveAccuracy μ δ N j / 2 := by
  unfold recursiveAccuracy
  rw [recursiveMass_succ]
  ring

end FreshGradientMinimax
