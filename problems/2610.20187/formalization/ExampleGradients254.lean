import LogisticExample254

noncomputable section
namespace Paper254

theorem linear_prediction_gradient {d : ℕ} (S : Set (Space d)) (L : Space d →L[ℝ] ℝ)
    (f : ℝ → ℝ) (a K : ℝ) (x : Space d) (hf : HasDerivAt f a (L x)) (ha : |a| ≤ K) :
    ∃ g : Space d,HasGradientWithinAt (fun w => f (L w)) g S x ∧ ‖g‖ ≤ K*‖L‖ := by
  have hd : HasFDerivAt (fun w => f (L w)) (a • L) x := hf.comp_hasFDerivAt x L.hasFDerivAt
  refine ⟨_,hd.hasFDerivWithinAt.hasGradientWithinAt,?_⟩
  rw [(InnerProductSpace.toDual ℝ (Space d)).symm.norm_map,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ha (norm_nonneg L)

theorem square_prediction_gradient {d : ℕ} (S : Set (Space d)) (L : Space d →L[ℝ] ℝ)
    (y B : ℝ) (x : Space d) (hx : |L x-y| ≤ B) :
    ∃ g : Space d,HasGradientWithinAt (fun w => 1/2*(L w-y)^2) g S x ∧ ‖g‖ ≤ B*‖L‖ := by
  apply linear_prediction_gradient S L (fun z => 1/2*(z-y)^2) (L x-y) B x _ hx
  convert (((hasDerivAt_id (L x)).sub_const y).pow 2).const_mul (1/2:ℝ) using 1 <;> dsimp <;> ring

theorem logistic_prediction_gradient {d : ℕ} (S : Set (Space d)) (L : Space d →L[ℝ] ℝ)
    (x : Space d) :
    ∃ g : Space d,HasGradientWithinAt (fun w => logisticLoss (L w)) g S x ∧ ‖g‖ ≤ ‖L‖ := by
  simpa only [one_mul] using linear_prediction_gradient S L logisticLoss (logisticFirst (L x)) 1 x
    (logistic_first (L x)) (logistic_gradient_bound (L x))

theorem portfolio_prediction_gradient {d : ℕ} (S : Set (Space d)) (L : Space d →L[ℝ] ℝ)
    (x : Space d) (b : ℝ) (hb : 0 < b) (hx : b ≤ L x) :
    ∃ g : Space d,HasGradientWithinAt (fun w => -Real.log (L w)) g S x ∧ ‖g‖ ≤ ‖L‖/b := by
  have hL : 0 < L x := hb.trans_le hx
  have hder : HasDerivAt (fun z : ℝ => -Real.log z) (-(L x)⁻¹) (L x) := (Real.hasDerivAt_log hL.ne').neg
  have hbound : |-(L x)⁻¹| ≤ 1/b := by
    rw [abs_neg,abs_of_pos (inv_pos.mpr hL)]
    simpa only [one_div] using one_div_le_one_div_of_le hb hx
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using
    linear_prediction_gradient S L (fun z => -Real.log z) (-(L x)⁻¹) (1/b) x hder hbound

end Paper254
#print axioms Paper254.square_prediction_gradient
#print axioms Paper254.logistic_prediction_gradient
#print axioms Paper254.portfolio_prediction_gradient
