import FreshGradientMinimax.RobinGreen

/-! Formula (35) for the actual inverse, together with coordinate bounds for
both endpoint-source columns. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robinSequence_monotone {n : ℕ} (hn : 10 ≤ n) : Monotone (robinSequence n) := by
  intro i j hij
  have ht0 : 0 ≤ (i : ℝ) * robinTheta n :=
    mul_nonneg (Nat.cast_nonneg _) (robinTheta_pos (n := n) (by omega)).le
  have hu0 : 0 ≤ (j : ℝ) * robinTheta n :=
    mul_nonneg (Nat.cast_nonneg _) (robinTheta_pos (n := n) (by omega)).le
  have ht : (i : ℝ) * robinTheta n ≤ (j : ℝ) * robinTheta n :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (robinTheta_pos (n := n) (by omega)).le
  have hc : Real.cosh ((i : ℝ) * robinTheta n) ≤ Real.cosh ((j : ℝ) * robinTheta n) :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg ht0, abs_of_nonneg hu0] using ht)
  exact add_le_add hc (mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr ht)
    (le_trans (by norm_num) (robin_parameters_bounds hn).2.2.2.1))

theorem robinGreen_coordinate_bounds {n i : ℕ} (hn : 10 ≤ n) (hi : i < n) :
    0 < robinSequence n i / robinBoundaryDenominator n ∧
      robinSequence n i / robinBoundaryDenominator n < n := by
  have hd := robinBoundaryDenominator_pos hn
  refine ⟨div_pos (lt_of_lt_of_le (by norm_num) (robinSequence_ge_one hn i)) hd, ?_⟩
  apply (div_lt_iff₀ hd).mpr
  exact (robinSequence_monotone hn (show i ≤ n - 1 by omega)).trans_lt
    (robinBoundaryDenominator_diagonal hn)

theorem robinInverse_first_bounds {n : ℕ} (hn : 10 ≤ n + 2) (i : Fin (n + 2)) :
    0 < robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i ∧
      robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i < n + 2 := by
  rw [robinInverse_first hn, robinGreenFirst_apply]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    robinGreen_coordinate_bounds hn (i := n + 2 - 1 - i.val) (by omega)

theorem robinInverse_last_bounds {n : ℕ} (hn : 10 ≤ n + 2) (i : Fin (n + 2)) :
    0 < robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i ∧
      robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i < n + 2 := by
  rw [robinInverse_last hn, robinGreenLast_apply]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using robinGreen_coordinate_bounds hn i.isLt

theorem robinInverse_entry_first {n : ℕ} (hn : 10 ≤ n + 2) :
    robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) 0 / (n + 2 : ℕ) =
      robinA1 (n + 2) := by
  rw [robinInverse_first hn, robinGreenFirst_apply]
  simp only [Fin.val_zero, Nat.sub_zero, robinA1]
  ring

theorem robinInverse_entry_cross {n : ℕ} (hn : 10 ≤ n + 2) :
    robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) 0 /
        (n + 2 : ℕ) = robinA2 (n + 2) := by
  rw [robinInverse_last hn, robinGreenLast_apply]
  simp only [Fin.val_zero, robinSequence_zero, robinA2]
  ring

theorem robinInverse_entry_last {n : ℕ} (hn : 10 ≤ n + 2) :
    robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1)
        (Fin.last (n + 1)) / (n + 2 : ℕ) = robinA1 (n + 2) := by
  rw [robinInverse_last hn, robinGreenLast_apply]
  simp only [Fin.val_last, robinA1, show n + 2 - 1 = n + 1 by omega]
  ring

theorem robinInverse_entry_cross_reverse {n : ℕ} (hn : 10 ≤ n + 2) :
    robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1)
        (Fin.last (n + 1)) / (n + 2 : ℕ) = robinA2 (n + 2) := by
  rw [robinInverse_first hn, robinGreenFirst_apply]
  simp only [Fin.val_last, show n + 2 - 1 - (n + 1) = 0 by omega,
    robinSequence_zero, robinA2]
  ring

theorem robin_actual_endpoint_bounds {n : ℕ} (hn : 10 ≤ n + 2) :
    let a₁ := robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) 0 / (n + 2 : ℕ)
    let a₂ := robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) 0 /
      (n + 2 : ℕ)
    1 / 7 ≤ a₂ ∧ a₂ ≤ a₁ ∧ a₁ < 1 ∧
      12 ≤ 12 / a₂ ∧ 12 / a₂ ≤ 84 ∧
      0 < (12 / a₂) * (1 + a₂ - a₁) / 2 ∧
      (12 / a₂) * (1 + a₂ - a₁) / 2 ≤ 42 := by
  dsimp only
  rw [robinInverse_entry_first hn, robinInverse_entry_cross hn]
  have ha := robin_endpoint_coefficient_bounds hn
  exact ⟨ha.1, ha.2.1, ha.2.2, robin_coefficients_bounds hn⟩

end FreshGradientMinimax
