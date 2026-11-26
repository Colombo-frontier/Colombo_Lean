import Bilevel.PublicRadialExtension

/-! Global second-derivative budget of the actual public radial extension,
including arbitrary and unbounded normal coordinates. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PublicRadialExtension
open RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem rank_norm_bound (u v : E) : ‖(innerSL ℝ u).smulRight v‖≤‖u‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  simp only [ContinuousLinearMap.smulRight_apply,innerSL_apply,norm_smul,Real.norm_eq_abs]
  convert mul_le_mul_of_nonneg_right (abs_real_inner_le_norm u w) (norm_nonneg v) using 1
  ring

omit [CompleteSpace E] in
theorem normal_hessian_term_bound (R : ℝ) (hR : 0<R) (e z : E) (he : ‖e‖≤1) :
    ‖⟪e,z⟫ • compressDerivative R z‖≤R := by
  rw [norm_smul ⟪e,z⟫ (compressDerivative R z),Real.norm_eq_abs]
  have hi : |⟪e,z⟫|≤‖z‖ := (abs_real_inner_le_norm e z).trans (by nlinarith [norm_nonneg z])
  have hh := mul_le_mul hi (compressDerivative_opNorm_le_scale R hR z)
    (norm_nonneg _) (norm_nonneg z)
  exact hh.trans (by simpa only [mul_comm] using compressed_radius_bound R hR z)

omit [CompleteSpace E] in
theorem hessianField_norm_bound (a R : ℝ) (ha : 0≤a) (hR : 0<R)
    (e z : E) (he : ‖e‖≤1) : ‖hessianField a R e z‖≤3*a := by
  have hb := compress_norm_le_radius R hR z
  have h1 : ‖(innerSL ℝ (compress R z)).smulRight e‖≤R :=
    (rank_norm_bound _ _).trans (by nlinarith [norm_nonneg (compress R z)])
  have h2 : ‖(innerSL ℝ e).smulRight (compress R z)‖≤R :=
    (rank_norm_bound _ _).trans (by nlinarith [norm_nonneg (compress R z)])
  have h3 := normal_hessian_term_bound R hR e z he
  unfold hessianField
  rw [norm_smul (a/R) ((innerSL ℝ (compress R z)).smulRight e+
    (innerSL ℝ e).smulRight (compress R z)+⟪e,z⟫ • compressDerivative R z),
    Real.norm_eq_abs,abs_of_nonneg (div_nonneg ha hR.le)]
  calc
    _ ≤ (a/R)*(3*R) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg ha hR.le)
      exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans (by linarith)
    _ = _ := by field_simp;ring

theorem actual_hessian_norm_bound (a R : ℝ) (ha : 0≤a) (hR : 0<R)
    (e z : E) (he : ‖e‖≤1) : ‖fderiv ℝ (gradient (potential a R e)) z‖≤3*a := by
  rw [actual_hessian a R hR e z]
  exact hessianField_norm_bound a R ha hR e z he

theorem actual_gradient_lipschitz (a R : ℝ) (ha : 0≤a) (hR : 0<R)
    (e : E) (he : ‖e‖≤1) :
    LipschitzWith ⟨3*a,by positivity⟩ (gradient (potential a R e)) := by
  rw [show gradient (potential a R e)=gradientField a R e from funext (potential_gradient a R hR e)]
  apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (gradientField_hasFDerivAt a R hR e z).differentiableAt)
  intro z
  rw [(gradientField_hasFDerivAt a R hR e z).fderiv]
  exact_mod_cast hessianField_norm_bound a R ha hR e z he

end Bilevel.PublicRadialExtension
