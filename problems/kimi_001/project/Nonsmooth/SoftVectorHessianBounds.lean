import Nonsmooth.SoftVectorPotentialCalculus

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem softVectorHessian_symmetric (ρ : ℝ) (f : ι → E → ℝ)
    (s : ι → E → E →L[ℝ] ℝ) (H : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ i x v w, H i x v w = H i x w v) (x v w : E) :
    softVectorHessian ρ f s H x v w = softVectorHessian ρ f s H x w v := by
  have hi (u w : E) : realInnerBilinear u w = inner ℝ u w := rfl
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => softplus_hessian_symmetric (f i x) (s i x) (H i x) (hsym i x) v w)
  simp only [softVectorHessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hi]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul] at hsum
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hsum, real_inner_comm v w]

theorem softVectorHessian_lower (ρ : ℝ) (f : ι → E → ℝ)
    (s : ι → E → E →L[ℝ] ℝ) (H : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hH : ∀ i x v, 0 ≤ H i x v v) (x v : E) :
    ρ * ‖v‖ ^ 2 ≤ softVectorHessian ρ f s H x v v := by
  have hi (u w : E) : realInnerBilinear u w = inner ℝ u w := rfl
  have hsum : 0 ≤ ∑ i, (softplusSlope (f i x) • H i x +
      softplusCurvature (f i x) • (s i x).smulRight (s i x)) v v :=
    Finset.sum_nonneg (fun i _ => softplus_hessian_nonnegative (f i x) (s i x) (H i x) (hH i x) v)
  simpa only [softVectorHessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hi,
    real_inner_self_eq_norm_sq, add_zero] using add_le_add (le_refl (ρ * ‖v‖ ^ 2)) hsum

theorem softplus_hessian_polynomial_bound (z : ℝ) (s : E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (x : E) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hs : ‖s‖ ≤ C * (1 + ‖x‖)) (hH : ‖H‖ ≤ D) :
    ‖softplusSlope z • H + softplusCurvature z • s.smulRight s‖ ≤
      (D + 2 * C ^ 2) * (1 + ‖x‖ ^ 2) := by
  have hs2 := (sq_le_sq₀ (norm_nonneg s) (by positivity : 0 ≤ C * (1 + ‖x‖))).mpr hs
  rw [mul_pow] at hs2
  have hp : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg C)
  have hn := softplus_hessian_norm_bound z s H
  nlinarith [mul_nonneg hD (sq_nonneg ‖x‖)]

theorem softVectorHessian_polynomial_bound (ρ : ℝ) (f : ι → E → ℝ)
    (s : ι → E → E →L[ℝ] ℝ) (H : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ i, 0 ≤ C i) (hD : ∀ i, 0 ≤ D i)
    (hs : ∀ i x, ‖s i x‖ ≤ C i * (1 + ‖x‖))
    (hH : ∀ i x, ‖H i x‖ ≤ D i) (x : E) :
    ‖softVectorHessian ρ f s H x‖ ≤
      (|ρ| * ‖realInnerBilinear (E := E)‖ + ∑ i, (D i + 2 * (C i) ^ 2)) * (1 + ‖x‖ ^ 2) := by
  let T := fun i => softplusSlope (f i x) • H i x +
    softplusCurvature (f i x) • (s i x).smulRight (s i x)
  have hsum : ‖∑ i, T i‖ ≤ (∑ i, (D i + 2 * (C i) ^ 2)) * (1 + ‖x‖ ^ 2) := by
    apply (norm_sum_le Finset.univ T).trans
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => softplus_hessian_polynomial_bound
      (f i x) (s i x) (H i x) x (hC i) (hD i) (hs i x) (hH i x))
  have hbase := ContinuousLinearMap.opNorm_smul_le ρ (realInnerBilinear (E := E))
  rw [Real.norm_eq_abs] at hbase
  have hn := norm_add_le (ρ • realInnerBilinear (E := E)) (∑ i, T i)
  change ‖ρ • realInnerBilinear (E := E) + ∑ i, T i‖ ≤ _
  nlinarith [mul_nonneg (mul_nonneg (abs_nonneg ρ) (norm_nonneg (realInnerBilinear (E := E))))
    (sq_nonneg ‖x‖)]

end
end Nonsmooth
