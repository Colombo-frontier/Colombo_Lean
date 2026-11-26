import SecondOrder.BoundedC21

namespace SecondOrder
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Riesz isometry preserves differences of Hessians, not only pointwise norms. -/
theorem norm_hessian_sub_eq_second_fderiv {f : H → ℝ} (hf : ContDiff ℝ 2 f) (x y : H) :
    ‖fderiv ℝ (gradient f) x-fderiv ℝ (gradient f) y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ := by
  let R := (InnerProductSpace.toDual ℝ H).symm.toLinearIsometry
  have hd (z : H) : fderiv ℝ (gradient f) z =
      R.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) z) :=
    (R.toContinuousLinearMap.hasFDerivAt.comp z
      (((hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable
        (by norm_num) z).hasFDerivAt)).fderiv
  rw [hd x,hd y,← ContinuousLinearMap.comp_sub]
  exact R.norm_toContinuousLinearMap_comp

theorem ScalarC21.hessian_lipschitz {f : H → ℝ} (hf : ScalarC21 f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      ‖fderiv ℝ (gradient f) x-fderiv ℝ (gradient f) y‖ ≤ L*‖x-y‖ := by
  simpa only [norm_hessian_sub_eq_second_fderiv hf.smooth] using hf.second_lipschitz

theorem scalarC21_of_hessian_lipschitz {f : H → ℝ} (hf : ContDiff ℝ 2 f)
    {L : ℝ} (hL : 0 ≤ L) (hl : ∀ x y,
      ‖fderiv ℝ (gradient f) x-fderiv ℝ (gradient f) y‖ ≤ L*‖x-y‖) : ScalarC21 f := by
  refine ⟨hf,L,hL,?_⟩
  simpa only [norm_hessian_sub_eq_second_fderiv hf] using hl

/-- Raw value, gradient, and Hessian bounds and a Lipschitz Hessian suffice;
no third derivative is assumed. -/
theorem boundedC21_of_hessian_bounds {f : H → ℝ} (hf : ContDiff ℝ 2 f)
    {C₀ C₁ C₂ L : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (hL : 0 ≤ L)
    (hb₀ : ∀ x, |f x| ≤ C₀) (hb₁ : ∀ x, ‖gradient f x‖ ≤ C₁)
    (hb₂ : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ C₂)
    (hl : ∀ x y, ‖fderiv ℝ (gradient f) x-fderiv ℝ (gradient f) y‖ ≤ L*‖x-y‖) :
    BoundedC21 f := by
  apply boundedC21_of_bounds hf h₀ h₁ h₂ hL
  · simpa only [Real.norm_eq_abs] using hb₀
  · simpa only [norm_gradient_eq_fderiv] using hb₁
  · simpa only [norm_hessian_eq_second_fderiv] using hb₂
  · simpa only [norm_hessian_sub_eq_second_fderiv hf] using hl

end
end SecondOrder
