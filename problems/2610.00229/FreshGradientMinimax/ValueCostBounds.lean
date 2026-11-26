import FreshGradientMinimax.CostedValueSolver

/-! Explicit accumulated expected-work bounds. The statistical coefficient
depends on the final accuracy but not on the initial energy; only the base
work is multiplied by the logarithmic epoch count. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem estimatorWork_nonneg (ℓ α ρ m e σ : ℝ) : 0 ≤ estimatorWork ℓ α ρ m e σ := by
  unfold estimatorWork multilevelWork
  apply add_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro j hj
  have hK : 0 < estimatorCutoff ρ m e σ := (Finset.mem_range.mp hj).trans_le' (Nat.zero_le j)
  exact mul_nonneg (level_probability_pos hK j).le (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem max_one_ceil_le {x : ℝ} (hx : 0 ≤ x) : (max 1 ⌈x⌉₊ : ℕ) ≤ 1 + x := by
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by have h := Nat.ceil_lt_add_one hx; linarith)

def epochBaseWork (ℓ α σ m H e : ℝ) : ℝ :=
  (epochSteps m H : ℝ) * estimatorWork ℓ α epochRho m e σ + refreshSteps ℓ α

def epochNoiseWork (ℓ α σ m H e : ℝ) : ℝ :=
  (epochSteps m H : ℝ) * estimatorWork ℓ α epochRho m e σ *
    (100000000 * 17 * (140 * (estimatorCutoff epochRho m e σ + 1 : ℝ) * σ ^ 2)) / Real.sqrt (m * H) +
  (refreshSteps ℓ α : ℝ) * (1000000 * σ ^ 2 * m) / (α * ℓ)

theorem epochBaseWork_nonneg (ℓ α σ m H e : ℝ) : 0 ≤ epochBaseWork ℓ α σ m H e :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _) (estimatorWork_nonneg _ _ _ _ _ _)) (Nat.cast_nonneg _)

theorem epochNoiseWork_nonneg {ℓ α σ m H e : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (hm : 0 < m) :
    0 ≤ epochNoiseWork ℓ α σ m H e := by
  unfold epochNoiseWork
  have hw := estimatorWork_nonneg ℓ α epochRho m e σ
  positivity

theorem fullEpochWork_bound {ℓ α σ m H e E : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hm : 0 < m) (hH : 0 < H) (hE : 0 < E) :
    fullEpochWork ℓ α σ m H e E ≤ epochBaseWork ℓ α σ m H e + epochNoiseWork ℓ α σ m H e / E := by
  have hs : 0 < Real.sqrt (m * H) := Real.sqrt_pos.mpr (mul_pos hm hH)
  have hb := max_one_ceil_le (by positivity : 0 ≤
    (100000000 * 17 * (140 * (estimatorCutoff epochRho m e σ + 1 : ℝ) * σ ^ 2)) / (E * Real.sqrt (m * H)))
  have hf := max_one_ceil_le (by positivity : 0 ≤ 1000000 * σ ^ 2 * m / (α * ℓ * E))
  have hw := estimatorWork_nonneg ℓ α epochRho m e σ
  have hbm := mul_le_mul_of_nonneg_left hb (mul_nonneg (Nat.cast_nonneg (epochSteps m H)) hw)
  have hfm := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (refreshSteps ℓ α))
  have heq :
      (epochSteps m H : ℝ) * estimatorWork ℓ α epochRho m e σ *
        (1 + (100000000 * 17 * (140 * (estimatorCutoff epochRho m e σ + 1 : ℝ) * σ ^ 2)) /
          (E * Real.sqrt (m * H))) +
      (refreshSteps ℓ α : ℝ) * (1 + 1000000 * σ ^ 2 * m / (α * ℓ * E)) =
      epochBaseWork ℓ α σ m H e + epochNoiseWork ℓ α σ m H e / E := by
    unfold epochBaseWork epochNoiseWork
    field_simp
    ring
  rw [← heq]
  change (epochSteps m H : ℝ) * (epochBatch m H e σ E : ℝ) * estimatorWork ℓ α epochRho m e σ +
    (refreshSteps ℓ α : ℝ) * (refreshBatch ℓ α σ m E : ℝ) ≤ _
  change (epochSteps m H : ℝ) * estimatorWork ℓ α epochRho m e σ * (epochBatch m H e σ E : ℝ) ≤ _ at hbm
  change (refreshSteps ℓ α : ℝ) * (refreshBatch ℓ α σ m E : ℝ) ≤ _ at hfm
  nlinarith only [hbm, hfm]

theorem valueSolverWork_bound {ℓ α σ m H e E₀ : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hm : 0 < m) (hH : 0 < H) (he : 0 < e) :
    valueSolverWork ℓ α σ m H e E₀ ≤
      epochBaseWork ℓ α σ m H e * (Real.log (max E₀ e / e) / Real.log 2 + 2) +
        4 * epochNoiseWork ℓ α σ m H e / e := by
  have hbase := epochBaseWork_nonneg ℓ α σ m H e
  have hnoise := epochNoiseWork_nonneg (σ := σ) (H := H) (e := e) hℓ hα hm
  have hsum := Finset.sum_le_sum (s := Finset.range (finalEpochIndex E₀ e + 1))
    (fun j _ => fullEpochWork_bound (σ := σ) (e := e) hℓ hα hm hH (he.trans_le (valueEnvelope_ge E₀ e j)))
  change valueSolverWork ℓ α σ m H e E₀ ≤ _ at hsum
  have hform : (∑ j ∈ Finset.range (finalEpochIndex E₀ e + 1),
      (epochBaseWork ℓ α σ m H e + epochNoiseWork ℓ α σ m H e / valueEnvelope E₀ e j)) =
      (finalEpochIndex E₀ e + 1 : ℕ) * epochBaseWork ℓ α σ m H e +
        epochNoiseWork ℓ α σ m H e * ∑ j ∈ Finset.range (finalEpochIndex E₀ e + 1), 1 / valueEnvelope E₀ e j := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hform] at hsum
  have hcount := mul_le_mul_of_nonneg_right (finalEpochIndex_count (E₀ := E₀) he) hbase
  have hinverse := mul_le_mul_of_nonneg_left (valueEnvelope_inverse_sum (E₀ := E₀) he) hnoise
  convert hsum.trans (add_le_add hcount hinverse) using 1
  ring

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem costedValueSolverKernel_random_work_bound (O : FreshOracle S.toNCObjective σ)
    {m H e E₀ : ℝ} (hm : 0 < m) (hH : 0 < H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) ≤
      epochBaseWork ℓ α σ m H e * (Real.log (max E₀ e / e) / Real.log 2 + 2) +
        4 * epochNoiseWork ℓ α σ m H e / e := by
  rw [(S.costedValueSolverKernel_random_cost O m H e E₀ r hr ν).2]
  exact valueSolverWork_bound S.toNCObjective.L_pos S.α_pos hm hH he

end SCObjective
end FreshGradientMinimax
