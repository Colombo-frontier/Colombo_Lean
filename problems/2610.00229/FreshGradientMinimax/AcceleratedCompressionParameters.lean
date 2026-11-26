import FreshGradientMinimax.PrimalParameters

/-! The original primal radius and smoothness constants in (39). -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def acceleratedRadiusConstant : ℝ := 10 ^ 4 * 10 ^ 8 / primalRidgeConstant
def acceleratedPrimalRadius (k : ℕ) : ℝ := acceleratedRadiusConstant * Real.sqrt (k + 1 : ℕ)
def acceleratedSmoothnessConstant : ℝ := 10 ^ 10

theorem acceleratedRadiusConstant_pos : 0 < acceleratedRadiusConstant :=
  div_pos (by norm_num) primalRidgeConstant_pos

theorem acceleratedPrimalRadius_pos (k : ℕ) : 0 < acceleratedPrimalRadius k :=
  mul_pos acceleratedRadiusConstant_pos (Real.sqrt_pos.mpr (by positivity))

theorem accelerated_radius_correction (k : ℕ) :
    3 * (10 ^ 8 * Real.sqrt (k + 1 : ℕ)) / acceleratedPrimalRadius k =
      3 * primalRidgeConstant / 10 ^ 4 := by
  have hs : Real.sqrt (k + 1 : ℕ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (k + 1 : ℕ))).ne'
  unfold acceleratedPrimalRadius acceleratedRadiusConstant
  field_simp [hs, primalRidgeConstant_pos.ne']
  ring

theorem accelerated_compression_xx_bound (k : ℕ) :
    10 ^ 8 + 3 * (10 ^ 8 * Real.sqrt (k + 1 : ℕ)) / acceleratedPrimalRadius k + primalRidgeConstant ≤
      acceleratedSmoothnessConstant / 2 := by
  rw [accelerated_radius_correction]
  unfold acceleratedSmoothnessConstant
  nlinarith only [primalRidgeConstant_le_one]

theorem accelerated_compression_other_bound : (10 ^ 8 : ℝ) ≤ acceleratedSmoothnessConstant / 2 := by
  norm_num [acceleratedSmoothnessConstant]

theorem acceleratedPrimalRadius_large (k : ℕ) :
    10 ^ 8 * Real.sqrt (k + 1 : ℕ) + primalRidgeConstant / 2 <
      primalRidgeConstant * (acceleratedPrimalRadius k / 2) := by
  have hs : 1 ≤ Real.sqrt (k + 1 : ℕ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ k + 1 by omega))
  have he : primalRidgeConstant * (acceleratedPrimalRadius k / 2) =
      (10 ^ 4 * 10 ^ 8 / 2 : ℝ) * Real.sqrt (k + 1 : ℕ) := by
    unfold acceleratedPrimalRadius acceleratedRadiusConstant
    field_simp [primalRidgeConstant_pos.ne']
    ring
  rw [he]
  nlinarith only [hs, primalRidgeConstant_le_one]

end FreshGradientMinimax

