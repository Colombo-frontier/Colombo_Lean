import FreshGradientMinimax.CoreTheta
import Mathlib.Data.Complex.ExponentialBounds

/-! The exact threshold gate Ψ from (22). These value and locality results do
not yet assert the global derivative estimates of Lemma C.1. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def coreGate (t : ℝ) : ℝ := if t ≤ 1 / 2 then 0 else Real.exp (1 - (2 * t - 1)⁻¹ ^ 2)

theorem coreGate_zero {t : ℝ} (ht : t ≤ 1 / 2) : coreGate t = 0 := by
  rw [coreGate, if_pos ht]

theorem coreGate_nonneg (t : ℝ) : 0 ≤ coreGate t := by
  unfold coreGate
  split_ifs
  · rfl
  · exact (Real.exp_pos _).le

theorem coreGate_le_three (t : ℝ) : coreGate t ≤ 3 := by
  unfold coreGate
  split_ifs
  · norm_num
  · have h : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ((2 * t - 1)⁻¹)])).trans h.le

theorem coreGate_one : coreGate 1 = 1 := by norm_num [coreGate]

theorem coreGate_one_le {t : ℝ} (ht : 1 ≤ t) : 1 ≤ coreGate t := by
  have hx : 1 ≤ 2 * t - 1 := by linarith
  have hx0 : 0 < 2 * t - 1 := by linarith
  have hi : (2 * t - 1)⁻¹ ≤ 1 := (inv_le_one₀ hx0).mpr hx
  have hi0 : 0 ≤ (2 * t - 1)⁻¹ := inv_nonneg.mpr hx0.le
  rw [coreGate, if_neg (by linarith : ¬t ≤ 1 / 2)]
  apply Real.one_le_exp_iff.mpr
  nlinarith

theorem coreGate_flat {t : ℝ} (ht : |t| ≤ 1 / 2) : coreGate t = 0 ∧ coreGate (-t) = 0 := by
  exact ⟨coreGate_zero ((le_abs_self t).trans ht),
    coreGate_zero ((neg_le_abs t).trans ht)⟩

theorem coreGate_disjoint (t : ℝ) : coreGate t = 0 ∨ coreGate (-t) = 0 := by
  by_cases ht : t ≤ 1 / 2
  · exact Or.inl (coreGate_zero ht)
  · exact Or.inr (coreGate_zero (by linarith))

theorem coreGate_measurable : Measurable coreGate := by
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  fun_prop

end FreshGradientMinimax
