import Bilevel.ZeroChainChildProfiles

/-! Dimension-independent approximation error of the exact flattened residual. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainFlatteningError
open ZeroChain ZeroChainPotential ZeroChainRegularity ZeroChainResidual ZeroChainResidualScaled
  ZeroChainFlatteningCutoff ZeroChainFlatteningMap ZeroChainFlatteningBounds ZeroChainChildProfiles

theorem phi_lip (s t : ℝ) : |phi s-phi t| ≤ Real.sqrt (Real.exp 1)*|s-t| :=
  scalar_lip_of_deriv_bound phi _ ((phi_contDiff 1).differentiable (by norm_num)) phi_first_bound s t

theorem child_error_bound {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |phi t-phi (flatten δ t)| ≤ 2*Real.sqrt (Real.exp 1)*δ := by
  exact (phi_lip t (flatten δ t)).trans (by
    nlinarith [mul_le_mul_of_nonneg_left (flatten_error_le hδ t) (Real.sqrt_nonneg (Real.exp 1))])

theorem negative_child_error_bound {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |phi (-t)-phi (-flatten δ t)| ≤ 2*Real.sqrt (Real.exp 1)*δ := by
  have h := phi_lip (-t) (-flatten δ t)
  simp only [neg_sub_neg, abs_sub_comm (flatten δ t) t] at h
  exact h.trans (by
    nlinarith [mul_le_mul_of_nonneg_left (flatten_error_le hδ t) (Real.sqrt_nonneg (Real.exp 1))])

def errorConstant : ℝ := 2*(1+2*Real.exp 1)*Real.sqrt (Real.exp 1)

theorem errorConstant_pos : 0 < errorConstant := by dsimp [errorConstant]; positivity

theorem normalized_error {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/16)
    (n : ℕ) (z : Space n) :
    |ZeroChainResidual.residual n z-ZeroChainResidual.residual n (flattenMap n δ z)| ≤ errorConstant*δ := by
  have he : ZeroChainResidual.residual n z-ZeroChainResidual.residual n (flattenMap n δ z) =
      rawChild n (fun t => phi t-phi (flatten δ t)) (fun t => phi (-t)-phi (-flatten δ t)) z := by
    dsimp [ZeroChainResidual.residual]
    rw [rawResidual_eq_rawChild, rawResidual_flattenMap_eq hδ hsmall, ← rawChild_sub]
    ring
  rw [he]
  have hh := rawChild_abs_bound n _ _ (2*Real.sqrt (Real.exp 1)*δ) (by positivity)
    (child_error_bound hδ) (negative_child_error_bound hδ) z
  exact hh.trans_eq (by dsimp [errorConstant]; ring)

theorem flattenMap_scale_commute (n : ℕ) (β δ : ℝ) (hβ : β ≠ 0) (hδ : δ ≠ 0) (z : Space n) :
    β⁻¹ • flattenMap n δ z = flattenMap n (δ/β) (β⁻¹ • z) := by
  ext j
  simp only [PiLp.smul_apply, smul_eq_mul, flattenMap, coordinateMap_apply, flatten]
  have he : (β⁻¹*z j)/(δ/β) = z j/δ := by field_simp
  rw [he]
  ring

theorem scaled_error (n : ℕ) (a β δ : ℝ) (ha : 0 ≤ a) (hβ : 0 < β) (hδ : 0 < δ)
    (hsmall : δ ≤ β/16) (z : Space n) :
    |R n a β z-flattenedResidual n a β δ z| ≤ errorConstant*a*δ/β := by
  change |a*ZeroChainResidual.residual n (β⁻¹ • z)-
    a*ZeroChainResidual.residual n (β⁻¹ • flattenMap n δ z)| ≤ _
  rw [flattenMap_scale_commute n β δ hβ.ne' hδ.ne', ← mul_sub, abs_mul, abs_of_nonneg ha]
  have hh := normalized_error (div_pos hδ hβ) ((div_le_iff₀ hβ).mpr (by linarith)) n (β⁻¹ • z)
  exact (mul_le_mul_of_nonneg_left hh ha).trans_eq (by ring)

/-- The paper's uniform approximation error CLβδ, proved without a factor
depending on the number of coordinates. -/
theorem source_flattening_error (n : ℕ) (η L β δ : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hL : 0 ≤ L) (hβ : 0 < β) (hδ : 0 < δ) (hsmall : δ ≤ β/16) (z : Space n) :
    |R n (η*L*β^2) β z-flattenedResidual n (η*L*β^2) β δ z| ≤ errorConstant*L*β*δ := by
  have hh := scaled_error n (η*L*β^2) β δ (by positivity) hβ hδ hsmall z
  have hm := mul_le_mul_of_nonneg_right hη1
    (show 0 ≤ errorConstant*L*β*δ by exact mul_nonneg (mul_nonneg (mul_nonneg errorConstant_pos.le hL) hβ.le) hδ.le)
  apply hh.trans
  convert hm using 1 <;> field_simp
  all_goals ring

end Bilevel.ZeroChainFlatteningError
