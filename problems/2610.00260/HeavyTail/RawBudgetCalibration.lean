import HeavyTail.AdaptiveKernelRejection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Explicit conversion of the raw-cap exponential tail to the stage's
confidence level. -/
namespace HeavyTail

theorem rawBudgetTail_le_exp (n : ℕ) :
    ((2 : ℝ) ^ (8 * n))⁻¹ ≤ Real.exp (-(n : ℝ)) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have he : ((2 : ℝ) ^ (8 * n))⁻¹ = Real.exp (-((8 * n : ℕ) : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [he]
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_left hlog hn
  push_cast
  nlinarith only [hm, hn]

theorem rawBudgetTail_le_confidence {α : ℝ} (hα : 0 < α) (n : ℕ)
    (hn : Real.log (3 / α) ≤ (n : ℝ)) :
    ((2 : ℝ) ^ (8 * n))⁻¹ ≤ α / 2 := by
  calc
    _ ≤ Real.exp (-(n : ℝ)) := rawBudgetTail_le_exp n
    _ ≤ Real.exp (-Real.log (3 / α)) := Real.exp_le_exp.mpr (neg_le_neg hn)
    _ = α / 3 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    _ ≤ α / 2 := by linarith

end HeavyTail
