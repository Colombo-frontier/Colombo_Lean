import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Radial projection onto a known norm ball does not increase estimation error. -/
noncomputable section
namespace Bilevel.Clipping
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def clip (C : ℝ) (v : E) : E := if ‖v‖ ≤ C then v else (C / ‖v‖) • v

theorem fixed (C : ℝ) (v : E) (hv : ‖v‖ ≤ C) : clip C v = v := by simp [clip, hv]

theorem bounded (C : ℝ) (hC : 0 ≤ C) (v : E) : ‖clip C v‖ ≤ C := by
  by_cases hv : ‖v‖ ≤ C
  · simpa [fixed C v hv] using hv
  · have hn : 0 < ‖v‖ := lt_of_le_of_lt hC (lt_of_not_ge hv)
    simp only [clip, if_neg hv, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hC hn.le), div_mul_cancel₀ _ hn.ne', le_refl]

theorem error_nonincreasing (C : ℝ) (hC : 0 ≤ C) (v u : E) (hu : ‖u‖ ≤ C) :
    ‖clip C v - u‖ ≤ ‖v - u‖ := by
  by_cases hv : ‖v‖ ≤ C
  · rw [fixed C v hv]
  · have hn : 0 < ‖v‖ := lt_of_le_of_lt hC (lt_of_not_ge hv)
    have ht : 0 ≤ C / ‖v‖ := div_nonneg hC hn.le
    have ht1 : C / ‖v‖ ≤ 1 := (div_le_one hn).mpr (le_of_not_ge hv)
    have htn : (C / ‖v‖) * ‖v‖ = C := div_mul_cancel₀ C hn.ne'
    have hi : ⟪v, u⟫ ≤ ‖v‖ * C :=
      (real_inner_le_norm v u).trans (mul_le_mul_of_nonneg_left hu hn.le)
    have hfac := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * (1 - C / ‖v‖) by linarith)
    have hc : (C / ‖v‖) * (‖v‖ * C) = C ^ 2 := by rw [← mul_assoc, htn]; ring
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [clip, if_neg hv, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht, htn, real_inner_smul_left]
    nlinarith [sq_nonneg (‖v‖ - C)]

theorem squared_error_nonincreasing (C : ℝ) (hC : 0 ≤ C) (v u : E) (hu : ‖u‖ ≤ C) :
    ‖clip C v - u‖ ^ 2 ≤ ‖v - u‖ ^ 2 :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (error_nonincreasing C hC v u hu)

end Bilevel.Clipping
