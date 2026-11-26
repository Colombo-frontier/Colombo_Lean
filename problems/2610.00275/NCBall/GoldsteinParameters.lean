import NCBall.AbsoluteParameters

/-! # The same absolute constants in the Goldstein regime -/

noncomputable section
namespace NCBall

theorem goldstein_scale_of_absolute {ε L : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ lowerConstant * L) :
    (4 * (2 * ε)) * (bumpConstant + 2) ≤ L / 4 := by
  have hC := bumpConstant_pos
  have he : lowerConstant * L * (52428800 * (bumpConstant + 2)) = L := by
    unfold lowerConstant
    field_simp
  have hm := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ 52428800 * (bumpConstant + 2) by positivity)
  rw [he] at hm
  nlinarith [mul_pos hε (show 0 < bumpConstant + 2 by positivity)]

theorem goldstein_regime_of_absolute {ε δ Δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hlarge : regimeConstant * δ * ε ≤ Δ) :
    200 * bumpConstant * (4 * (2 * ε)) ^ 2 ≤ (ε / δ) * Δ := by
  have hC := bumpConstant_pos
  have hm := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ ε / δ by positivity)
  have he : (ε / δ) * (regimeConstant * δ * ε) = regimeConstant * ε ^ 2 := by
    field_simp
    ring
  rw [he] at hm
  unfold regimeConstant at hm
  nlinarith [mul_nonneg hC.le (sq_nonneg ε)]

theorem goldstein_dimension_of_absolute {n : ℕ} {ε δ Δ L : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hΔ : 0 ≤ Δ)
    (hd : regimeConstant * Real.log (2 + Δ * L ^ 2 / (δ * ε ^ 3)) ≤ (n : ℝ) + 1) :
    0 < n ∧ 12800 * Real.log (2 + (ε / δ) * Δ * L ^ 2 / (2 * ε) ^ 4) ≤ n := by
  have hA : 0 ≤ Δ * L ^ 2 / (δ * ε ^ 3) := by positivity
  have hn := transverse_dimension_of_absolute hA hd
  refine ⟨hn.1, le_trans ?_ hn.2⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 12800)
  apply Real.log_le_log (by positivity)
  have he : (ε / δ) * Δ * L ^ 2 / (2 * ε) ^ 4 = (Δ * L ^ 2 / (δ * ε ^ 3)) / 16 := by
    field_simp
    ring
  rw [he]
  linarith

theorem goldstein_coefficient_of_absolute {n : ℕ} {ε δ Δ L : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) :
    lowerConstant * (((n : ℝ) + 1) * L ^ 2 * Δ / (δ * ε ^ 3)) ≤
      ((n : ℝ) + 1) * L ^ 2 * Δ / (52428800 * bumpConstant * δ * ε ^ 3) := by
  have hC := bumpConstant_pos
  have hh := one_div_le_one_div_of_le (show 0 < 52428800 * bumpConstant by positivity)
    (show 52428800 * bumpConstant ≤ 52428800 * (bumpConstant + 2) by linarith)
  have hm := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ ((n : ℝ) + 1) * L ^ 2 * Δ / (δ * ε ^ 3) by positivity)
  convert hm using 1
  ring

end NCBall
