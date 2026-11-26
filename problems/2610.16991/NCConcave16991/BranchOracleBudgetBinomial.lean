import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds

/-! # The proved exponential binomial bound for the public branch budget -/

noncomputable section

namespace NCConcave16991.BranchOracleBudget

theorem factorial_lower (H : ℕ) (hH : 0 < H) :
    ((H : ℝ) / Real.exp 1) ^ H ≤ (H.factorial : ℝ) := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hb : (1 : ℝ) ≤ 2 * Real.pi * H := by nlinarith [Real.two_le_pi]
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * H) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hb
  calc
    ((H : ℝ) / Real.exp 1) ^ H ≤ Real.sqrt (2 * Real.pi * H) * ((H : ℝ) / Real.exp 1) ^ H := by
      nlinarith [pow_nonneg (div_nonneg (Nat.cast_nonneg H) (Real.exp_pos 1).le) H]
    _ ≤ _ := Stirling.le_factorial_stirling H

theorem choose_le_exp_pow (K H : ℕ) (hH : 0 < H) :
    (K.choose H : ℝ) ≤ (Real.exp 1 * K / H) ^ H := by
  have hp : 0 < (H : ℝ) / Real.exp 1 := div_pos (by exact_mod_cast hH) (Real.exp_pos 1)
  calc
    (K.choose H : ℝ) ≤ (K : ℝ) ^ H / (H.factorial : ℝ) := Nat.choose_le_pow_div H K
    _ ≤ (K : ℝ) ^ H / (((H : ℝ) / Real.exp 1) ^ H) :=
      div_le_div_of_nonneg_left (pow_nonneg (Nat.cast_nonneg K) _) (pow_pos hp _) (factorial_lower H hH)
    _ = _ := by
      rw [← div_pow]
      congr 1
      field_simp

end NCConcave16991.BranchOracleBudget
