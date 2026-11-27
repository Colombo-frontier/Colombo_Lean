import UpperOptimization

/-! First-order convexity and the exact shrinkage comparator used in U8--U9. -/

open Set InnerProductSpace

namespace Task006.Full

theorem convex_gradient_gap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) {x z v : E} (hx : x ∈ K) (hz : z ∈ K)
    (hg : HasGradientAt f v x) : f x - f z ≤ inner ℝ (x - z) v := by
  have hlineConvex : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ AffineMap.lineMap x z) :=
    (hf.comp_affineMap (AffineMap.lineMap x z)).subset
      (hf.1.mapsTo_lineMap hx hz) (convex_Icc _ _)
  have hline : HasDerivAt (fun t : ℝ => AffineMap.lineMap x z t) (z - x) 0 := by
    simpa [AffineMap.lineMap_apply_module'] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (z - x)).add_const x
  have hF : HasFDerivAt f (toDual ℝ E v) (AffineMap.lineMap x z (0 : ℝ)) := by
    simpa using hg.hasFDerivAt
  have hderiv : HasDerivAt (f ∘ AffineMap.lineMap x z) (inner ℝ v (z - x)) (0 : ℝ) := by
    convert! HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF hline using 1
  have hs := hlineConvex.le_slope_of_hasDerivAt
    (x := 0) (y := 1) (by simp) (by simp) (by norm_num) hderiv
  simp only [slope, sub_zero, inv_one, one_smul, vsub_eq_sub, Function.comp_apply,
    AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, inner_sub_right] at hs
  rw [real_inner_comm v (x - z), inner_sub_right]
  linarith

theorem shrink_comparator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ) (hκR : κ ≤ R)
    {x : E} (hx : ‖x‖ ≤ R) :
    ‖(1 - κ / R) • x‖ ≤ R - κ ∧ ‖(1 - κ / R) • x - x‖ ≤ κ := by
  have hfactor : 0 ≤ 1 - κ / R := by
    have := (div_le_one hR).mpr hκR
    linarith
  have hrmul : (1 - κ / R) * R = R - κ := by field_simp [hR.ne']
  have hnorm : ‖(1 - κ / R) • x‖ ≤ R - κ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfactor]
    exact (mul_le_mul_of_nonneg_left hx hfactor).trans_eq hrmul
  refine ⟨hnorm, ?_⟩
  have hid : (1 - κ / R) • x - x = -(κ / R) • x := by
    rw [sub_smul, one_smul, neg_smul]
    abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (div_nonneg hκ hR.le)]
  calc
    κ / R * ‖x‖ ≤ κ / R * R := mul_le_mul_of_nonneg_left hx (div_nonneg hκ hR.le)
    _ = κ := div_mul_cancel₀ _ hR.ne'

#print axioms convex_gradient_gap
#print axioms shrink_comparator

end Task006.Full
