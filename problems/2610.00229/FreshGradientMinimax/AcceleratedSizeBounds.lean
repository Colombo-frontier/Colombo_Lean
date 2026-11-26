import FreshGradientMinimax.AcceleratedFloorParameters
import FreshGradientMinimax.AcceleratedStages

/-! Exact sizes of the physical accelerated construction. These are size
estimates only; the oracle lower bound additionally needs adaptive hiding. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def acceleratedStageCoefficient : ℝ :=
  (8000 * Real.sqrt acceleratedSmoothnessConstant * acceleratedValueCoefficient)⁻¹

theorem acceleratedStageCoefficient_pos : 0 < acceleratedStageCoefficient :=
  inv_pos.mpr (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr acceleratedSmoothnessConstant_pos))
    acceleratedValueCoefficient_pos)

theorem acceleratedStageCount_ge_four {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k) :
    4 ≤ acceleratedStageCount n k := by
  have hn' : 12 ≤ n + 4 := by omega
  have h := Nat.mul_le_mul (show 1 ≤ k by omega) hn'
  simpa only [one_mul] using (show 4 ≤ 1 * 12 by norm_num).trans h

theorem accelerated_stage_size_bound (p : Parameters) {n k : ℕ}
    (hn : Real.sqrt p.κ / (4 * Real.sqrt acceleratedSmoothnessConstant) ≤ (n + 2 : ℝ))
    (hk : p.gap / (2000 * acceleratedValueScale p.L p.ε) ≤ (k : ℝ)) :
    acceleratedStageCoefficient * p.deterministic ≤ (acceleratedStageCount n k : ℝ) := by
  have hL := p.μ_pos.trans_le p.μ_le_L
  have hlam := acceleratedValueScale_pos hL p.ε_pos
  have h := mul_le_mul hn hk (div_nonneg p.gap_nonneg (by positivity)) (by positivity : (0 : ℝ) ≤ n + 2)
  have he : Real.sqrt p.κ / (4 * Real.sqrt acceleratedSmoothnessConstant) *
      (p.gap / (2000 * acceleratedValueScale p.L p.ε)) = acceleratedStageCoefficient * p.deterministic := by
    rw [acceleratedValueScale_coefficient]
    unfold acceleratedStageCoefficient Parameters.deterministic
    field_simp [hL.ne', p.ε_pos.ne', acceleratedValueCoefficient_pos.ne',
      (Real.sqrt_pos.mpr acceleratedSmoothnessConstant_pos).ne']
    ring
  rw [he] at h
  unfold acceleratedStageCount
  push_cast
  nlinarith only [h, Nat.cast_nonneg (α := ℝ) k]

theorem accelerated_horizon_size_bound (p : Parameters) {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (hsize : acceleratedStageCoefficient * p.deterministic ≤ (acceleratedStageCount n k : ℝ)) :
    (acceleratedStageCoefficient / 4) * p.deterministic ≤ ((acceleratedStageCount n k : ℝ) - 2) / 2 := by
  have hS : (4 : ℝ) ≤ acceleratedStageCount n k := by exact_mod_cast acceleratedStageCount_ge_four hn hk
  nlinarith only [hsize, hS]

theorem accelerated_physical_parameters (p : Parameters)
    (hκ : acceleratedConditionThreshold ≤ p.κ)
    (hgap : acceleratedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    ∃ n k : ℕ, 10 ≤ n + 2 ∧ 0 < k ∧
      n + 2 = ⌊Real.sqrt (p.κ / (4 * acceleratedSmoothnessConstant))⌋₊ ∧
      k + 1 = ⌊p.gap / (1000 * acceleratedValueScale p.L p.ε)⌋₊ ∧
      (n + 2 : ℝ) ^ 2 ≤ p.L / (4 * acceleratedSmoothnessConstant * p.μ) ∧
      1000 * (k + 1 : ℕ) * acceleratedValueScale p.L p.ε ≤ p.gap ∧
      (acceleratedStageCoefficient / 4) * p.deterministic ≤ ((acceleratedStageCount n k : ℝ) - 2) / 2 := by
  obtain ⟨n, hn, hnf, hnq, hnl⟩ := accelerated_chain_count_exists p hκ
  obtain ⟨k, hk, hkf, hkg, hkl⟩ := accelerated_stage_count_exists
    (acceleratedValueScale_pos (p.μ_pos.trans_le p.μ_le_L) p.ε_pos) (accelerated_gap_threshold_scale p hgap)
  exact ⟨n, k, hn, hk, hnf, hkf, hnq, hkg,
    accelerated_horizon_size_bound p hn hk (accelerated_stage_size_bound p hnl hkl)⟩

end FreshGradientMinimax
