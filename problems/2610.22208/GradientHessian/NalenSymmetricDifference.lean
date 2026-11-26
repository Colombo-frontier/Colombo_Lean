import GradientHessian.NalenFiniteDifference
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Symmetric finite-difference snapshots with an actual operator-norm
error bound. The decoder is continuous in its finitely many gradient
replies, so the construction is usable by an ordinary-query policy. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def symmetricPart (A : E →L[ℝ] E) : E →L[ℝ] E :=
  (1/2 : ℝ) • (A+ContinuousLinearMap.adjoint A)

theorem symmetricPart_continuous : Continuous (symmetricPart (E := E)) :=
  (continuous_id.add ContinuousLinearMap.adjoint.continuous).const_smul (1/2 : ℝ)

theorem symmetricPart_symmetric (A : E →L[ℝ] E) (x y : E) :
    ⟪symmetricPart A x,y⟫_ℝ=⟪x,symmetricPart A y⟫_ℝ := by
  simp only [symmetricPart,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    real_inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
  ring

theorem symmetricPart_norm_le (A : E →L[ℝ] E) : ‖symmetricPart A‖ ≤ ‖A‖ := by
  have h := norm_add_le A (ContinuousLinearMap.adjoint A)
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  have hs := ContinuousLinearMap.opNorm_smul_le (1/2 : ℝ) (A+ContinuousLinearMap.adjoint A)
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at hs
  change ‖(1/2 : ℝ) • (A+ContinuousLinearMap.adjoint A)‖ ≤ _
  linarith only [hs,h]

theorem hessianOperator_adjoint {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) :
    ContinuousLinearMap.adjoint (hessianOperator f z)=hessianOperator f z := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (hessianOperator_symmetric hf z x y).symm

theorem symmetricPart_error {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) (A : E →L[ℝ] E) :
    ‖symmetricPart A-hessianOperator f z‖ ≤ ‖A-hessianOperator f z‖ := by
  have he : symmetricPart A-hessianOperator f z=symmetricPart (A-hessianOperator f z) := by
    simp only [symmetricPart,map_sub,hessianOperator_adjoint hf z]
    module
  rw [he]
  exact symmetricPart_norm_le _

variable {I : Type*} [Fintype I] [DecidableEq I]

def differenceStep (I : Type*) [Fintype I] (δ : ℝ) : ℝ := δ/Real.sqrt (Fintype.card I)

def approximateFromGradients (b : OrthonormalBasis I ℝ E) (δ : ℝ) (g₀ : E) (g : I → E) : E →L[ℝ] E :=
  symmetricPart (columnOperator b (fun i => (differenceStep I δ)⁻¹ • (g i-g₀)))

omit [DecidableEq I] in
theorem approximateFromGradients_continuous (b : OrthonormalBasis I ℝ E) (δ : ℝ) :
    Continuous (fun p : E × (I → E) => approximateFromGradients b δ p.1 p.2) := by
  have hc : Continuous (fun p : E × (I → E) => fun i => (differenceStep I δ)⁻¹ • (p.2 i-p.1)) := by
    fun_prop
  exact symmetricPart_continuous.comp ((columnOperator_continuous b).comp hc)

omit [DecidableEq I] in
theorem approximateFromGradients_symmetric (b : OrthonormalBasis I ℝ E) (δ : ℝ)
    (g₀ : E) (g : I → E) (x y : E) :
    ⟪approximateFromGradients b δ g₀ g x,y⟫_ℝ=⟪x,approximateFromGradients b δ g₀ g y⟫_ℝ :=
  symmetricPart_symmetric _ _ _

theorem approximateFromGradients_error [Nonempty I] (b : OrthonormalBasis I ℝ E)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f)))
    (z : E) {δ : ℝ} (hδ : 0 < δ) :
    ‖approximateFromGradients b δ (gradient f z)
      (fun i => gradient f (z+differenceStep I δ • b i))-hessianOperator f z‖ ≤ δ := by
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hsqrt : 0 < Real.sqrt (Fintype.card I) := Real.sqrt_pos.mpr hcard
  have ha : 0 < differenceStep I δ := div_pos hδ hsqrt
  have h := (symmetricPart_error hf z (finiteDifference b f z (differenceStep I δ))).trans
    (finiteDifference_error b hf hL z ha)
  have he : Real.sqrt (Fintype.card I)*differenceStep I δ=δ := by
    unfold differenceStep
    field_simp
  rw [he] at h
  exact h

end GradientHessian.Nalen
