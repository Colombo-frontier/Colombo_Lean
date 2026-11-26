import SampleReuse.OracleGradientBatchConfidence
import SampleReuse.TreeEstimator

/-! A common explicit ceiling-batch scale for both derivative estimators.
This connects the verified confidence premises to the same `batchSize`
whose exact integer costs are used by the stopping-time charging theorem. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def confidenceBatchScale (d : ℕ) (η δ : ℝ) : ℝ :=
  128 * (matrixMomentOrder (d + 1) δ : ℝ) / η^2

theorem confidenceBatchScale_nonneg (d : ℕ) (η δ : ℝ) :
    0 ≤ confidenceBatchScale d η δ := by unfold confidenceBatchScale; positivity

theorem batchSize_mul_sq_sufficient (c w : ℝ) {η : ℝ} (hη : 0 < η) :
    c * w ≤ (batchSize (c / η^2) w : ℝ) * η^2 := by
  have hb := mul_le_mul_of_nonneg_right (batchSize_sufficient (c / η^2) w) (sq_nonneg η)
  have he : (c / η^2 * w) * η^2 = c * w := by
    field_simp
  simpa only [he] using hb

theorem min_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b)^2 = min (a^2) (b^2) := by
  rcases le_total a b with hab | hba
  · simp only [min_eq_left hab, min_eq_left (pow_le_pow_left₀ ha hab 2)]
  · simp only [min_eq_right hba, min_eq_right (pow_le_pow_left₀ hb hba 2)]

theorem confidenceBatchSize_gradient_edge {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {η δ σ L : ℝ} (hη : 0 < η) (hσ : 0 ≤ σ) (hL : 0 ≤ L) (x y : E) :
    32 * (matrixMomentOrder (d + 1) δ : ℝ) * (2 * min σ (L * ‖x-y‖))^2 ≤
      (batchSize (confidenceBatchScale d η δ) (min (σ^2) (L^2 * ‖x-y‖^2)) : ℝ) * η^2 := by
  have hm : min (σ^2) (L^2 * ‖x-y‖^2) = (min σ (L * ‖x-y‖))^2 := by
    rw [min_sq_of_nonneg hσ (mul_nonneg hL (norm_nonneg _)), mul_pow]
  have hs := batchSize_mul_sq_sufficient (128 * (matrixMomentOrder (d + 1) δ : ℝ))
    (min (σ^2) (L^2 * ‖x-y‖^2)) hη
  change 128 * (matrixMomentOrder (d + 1) δ : ℝ) * _ ≤
    (batchSize (confidenceBatchScale d η δ) _ : ℝ) * η^2 at hs
  rw [hm] at hs ⊢
  nlinarith

theorem confidenceBatchSize_hessian_edge {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) {η δ σ L : ℝ} (hη : 0 < η) (hσ : 0 ≤ σ) (hL : 0 ≤ L) (x y : E) :
    8 * (matrixMomentOrder (d + 1) δ : ℝ) * (2 * min σ (L * ‖x-y‖))^2 ≤
      (batchSize (confidenceBatchScale d η δ) (min (σ^2) (L^2 * ‖x-y‖^2)) : ℝ) * η^2 := by
  have hs := confidenceBatchSize_gradient_edge d hη hσ hL x y (δ := δ)
  have hk : 0 ≤ (matrixMomentOrder (d + 1) δ : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg (2 * min σ (L * ‖x-y‖))]

theorem confidenceBatchSize_gradient_root (d : ℕ) {η δ σ : ℝ} (hη : 0 < η) :
    32 * (matrixMomentOrder (d + 1) δ : ℝ) * σ^2 ≤
      (batchSize (confidenceBatchScale d η δ) (σ^2) : ℝ) * η^2 := by
  have hs := batchSize_mul_sq_sufficient (128 * (matrixMomentOrder (d + 1) δ : ℝ)) (σ^2) hη
  change 128 * (matrixMomentOrder (d + 1) δ : ℝ) * σ^2 ≤
    (batchSize (confidenceBatchScale d η δ) (σ^2) : ℝ) * η^2 at hs
  have hk : 0 ≤ (matrixMomentOrder (d + 1) δ : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg σ]

theorem confidenceBatchSize_hessian_root (d : ℕ) {η δ σ : ℝ} (hη : 0 < η) :
    8 * (matrixMomentOrder (d + 1) δ : ℝ) * σ^2 ≤
      (batchSize (confidenceBatchScale d η δ) (σ^2) : ℝ) * η^2 := by
  have hs := confidenceBatchSize_gradient_root d (δ := δ) (σ := σ) hη
  have hk : 0 ≤ (matrixMomentOrder (d + 1) δ : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg σ]

end
end SampleReuse
