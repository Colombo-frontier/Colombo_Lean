import NCBall.UniformDimension

/-! # One pair of absolute constants for both lower-bound regimes -/

noncomputable section
namespace NCBall

def lowerConstant : ℝ := 1 / (52428800 * (bumpConstant + 2))
def regimeConstant : ℝ := 40000 * (bumpConstant + 2)

theorem lowerConstant_pos : 0 < lowerConstant := by
  have := bumpConstant_pos
  unfold lowerConstant
  positivity

theorem regimeConstant_pos : 0 < regimeConstant := by
  have := bumpConstant_pos
  unfold regimeConstant
  positivity

theorem accuracy_scale_of_absolute {η L : ℝ} (hη : 0 < η)
    (hsmall : η ≤ lowerConstant * L) :
    (4 * η) * (bumpConstant + 2) ≤ L / 4 := by
  have hC := bumpConstant_pos
  have he : lowerConstant * (52428800 * (bumpConstant + 2)) = 1 := by
    unfold lowerConstant
    field_simp
  have hm := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ 52428800 * (bumpConstant + 2) by positivity)
  have he' : lowerConstant * L * (52428800 * (bumpConstant + 2)) = L := by
    calc
      _ = (lowerConstant * (52428800 * (bumpConstant + 2))) * L := by ring
      _ = _ := by rw [he, one_mul]
  rw [he'] at hm
  nlinarith [mul_pos hη (show 0 < bumpConstant + 2 by positivity)]

theorem depth_regime_of_absolute {η H Δ : ℝ}
    (hlarge : regimeConstant * η ^ 2 ≤ H * Δ) :
    200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ := by
  have hC := bumpConstant_pos
  unfold regimeConstant at hlarge
  nlinarith [mul_nonneg hC.le (sq_nonneg η)]

theorem transverse_dimension_of_absolute {n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hd : regimeConstant * Real.log (2 + A) ≤ (n : ℝ) + 1) :
    0 < n ∧ 12800 * Real.log (2 + A) ≤ n := by
  have hl := log_two_add_lower hA
  have hC := bumpConstant_ge_one
  have hreg : 120000 ≤ regimeConstant := by unfold regimeConstant; linarith
  have hprod := mul_le_mul_of_nonneg_right hreg (by linarith : 0 ≤ Real.log (2 + A))
  have hnlarge : (59999 : ℝ) ≤ n := by linarith
  constructor
  · have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  · linarith

theorem smooth_coefficient_of_absolute {n : ℕ} {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) :
    lowerConstant * (((n : ℝ) + 1) * L ^ 2 * H * Δ / η ^ 4) ≤
      ((n : ℝ) + 1) * L ^ 2 * H * Δ / (3276800 * bumpConstant * η ^ 4) := by
  have hC := bumpConstant_pos
  have hd : 3276800 * bumpConstant ≤ 52428800 * (bumpConstant + 2) := by linarith
  have hh := one_div_le_one_div_of_le (show 0 < 3276800 * bumpConstant by positivity) hd
  have hm := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ ((n : ℝ) + 1) * L ^ 2 * H * Δ / η ^ 4 by positivity)
  convert hm using 1
  ring

end NCBall
