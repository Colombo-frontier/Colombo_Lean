import GradientHessian.NalenObjective
import GradientHessian.NalenSubproblem

/-! Actual second-order Taylor and midpoint descent estimates for C2
objectives with Lipschitz Hessians. Quadratic terms cancel at the midpoint,
so no bound on the Hessian itself is needed. -/

noncomputable section
namespace GradientHessian.Nalen
open Set Metric InnerProductSpace
open scoped InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def taylorPolynomial (f : E → ℝ) (x y : E) : ℝ :=
  quadraticModel (gradient f x) ((2 : ℝ) • hessianOperator f x) x 0 0 y+
    (f x-⟪gradient f x,x⟫_ℝ)

theorem taylorPolynomial_apply (f : E → ℝ) (x y : E) :
    taylorPolynomial f x y=f x+⟪gradient f x,y-x⟫_ℝ+
      (1/2 : ℝ)*⟪hessianOperator f x (y-x),y-x⟫_ℝ := by
  simp only [taylorPolynomial,quadraticModel,ContinuousLinearMap.smul_apply,
    real_inner_smul_left,inner_sub_right,mul_zero,div_zero,zero_mul]
  ring

@[simp] theorem taylorPolynomial_self (f : E → ℝ) (x : E) : taylorPolynomial f x x=f x := by
  simp [taylorPolynomial_apply]

theorem taylorPolynomial_hasFDerivAt {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x y : E) :
    HasFDerivAt (taylorPolynomial f x)
      (innerSL ℝ (gradient f x+hessianOperator f x (y-x))) y := by
  have hB : ∀ u v,⟪((2 : ℝ) • hessianOperator f x) u,v⟫_ℝ=⟪u,((2 : ℝ) • hessianOperator f x) v⟫_ℝ := by
    intro u v
    simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left,inner_smul_right]
    rw [hessianOperator_symmetric hf]
  have h := (quadraticModel_hasFDerivAt (gradient f x) ((2 : ℝ) • hessianOperator f x) x 0 0 hB y).add_const
    (f x-⟪gradient f x,x⟫_ℝ)
  convert h using 1
  simp [ContinuousLinearMap.smul_apply,smul_smul]

theorem taylor_remainder_derivative_norm {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x y : E) :
    ‖fderiv ℝ (fun z => f z-taylorPolynomial f x z) y‖ =
      ‖gradient f y-gradient f x-hessianOperator f x (y-x)‖ := by
  have hd := ((hf.differentiable (by norm_num)) y).hasFDerivAt.sub
    (taylorPolynomial_hasFDerivAt hf x y)
  rw [hd.fderiv]
  have he : fderiv ℝ f y-innerSL ℝ (gradient f x+hessianOperator f x (y-x)) =
      (toDual ℝ E) (gradient f y-gradient f x-hessianOperator f x (y-x)) := by
    ext u
    simp only [ContinuousLinearMap.sub_apply,innerSL_apply,toDual_apply,inner_add_left,inner_sub_left,
      gradient,toDual_symm_apply]
    ring
  rw [he,(toDual ℝ E).norm_map]

theorem second_taylor_remainder {f : E → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ f))) (x y : E) :
    ‖f y-taylorPolynomial f x y‖ ≤ (L : ℝ)*‖y-x‖^3 := by
  let r := fun z => f z-taylorPolynomial f x z
  have hd (z : E) : DifferentiableAt ℝ r z :=
    ((hf.differentiable (by norm_num)) z).sub (taylorPolynomial_hasFDerivAt hf x z).differentiableAt
  have hb (z : E) (hz : z ∈ closedBall x ‖y-x‖) :
      ‖fderiv ℝ r z‖ ≤ (L : ℝ)*‖y-x‖^2 := by
    rw [taylor_remainder_derivative_norm hf x z]
    apply (gradient_taylor hf hL x z).trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z) hb
    (convex_closedBall x ‖y-x‖) (mem_closedBall_self (norm_nonneg _))
    (show y ∈ closedBall x ‖y-x‖ by simp [mem_closedBall,dist_eq_norm])
  have hx : r x=0 := by simp [r]
  rw [hx,sub_zero] at h
  change ‖r y‖ ≤ _
  calc
    ‖r y‖ ≤ (L : ℝ)*‖y-x‖^2*‖y-x‖ := h
    _ = _ := by ring

theorem midpoint_descent_error {f : E → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ f))) (x δ : E) :
    ‖f (x+δ)-f x-⟪gradient f (x+(1/2 : ℝ) • δ),δ⟫_ℝ‖ ≤ (L : ℝ)/4*‖δ‖^3 := by
  let c := x+(1/2 : ℝ) • δ
  have hp : x+δ-c=(1/2 : ℝ) • δ := by dsimp [c]; module
  have hm : x-c=-((1/2 : ℝ) • δ) := by dsimp [c]; module
  have hpoly : taylorPolynomial f c (x+δ)-taylorPolynomial f c x=⟪gradient f c,δ⟫_ℝ := by
    rw [taylorPolynomial_apply,taylorPolynomial_apply,hp,hm]
    simp only [inner_smul_right,map_smul,map_neg,inner_neg_left,inner_neg_right,
      real_inner_smul_left]
    ring
  have h₁ := second_taylor_remainder hf hL c (x+δ)
  have h₀ := second_taylor_remainder hf hL c x
  rw [hp,norm_smul] at h₁
  rw [hm,norm_neg,norm_smul] at h₀
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at h₁ h₀
  have he : f (x+δ)-f x-⟪gradient f c,δ⟫_ℝ =
      (f (x+δ)-taylorPolynomial f c (x+δ))-(f x-taylorPolynomial f c x) := by
    rw [← hpoly]
    ring
  change ‖f (x+δ)-f x-⟪gradient f c,δ⟫_ℝ‖ ≤ _
  rw [he]
  have h := norm_sub_le (f (x+δ)-taylorPolynomial f c (x+δ)) (f x-taylorPolynomial f c x)
  simp only [Real.norm_eq_abs] at h ⊢
  nlinarith only [h,h₁,h₀]

end GradientHessian.Nalen
