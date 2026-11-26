import SampleReuse.Model
import SecondOrder.ScalarLinearScaling
import Mathlib.Analysis.InnerProductSpace.Adjoint

open SecondOrder
open scoped InnerProductSpace

namespace SampleReuse
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def isometryProjection (U : E →ₗᵢ[ℝ] F) : F →L[ℝ] E := U.toContinuousLinearMap.adjoint
def paddedLoss (U : E →ₗᵢ[ℝ] F) (f : E → ℝ) : F → ℝ := f ∘ isometryProjection U

theorem isometryProjection_norm (U : E →ₗᵢ[ℝ] F) : ‖isometryProjection U‖ ≤ 1 := by
  unfold isometryProjection
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using (U.norm_map x).le

theorem isometryProjection_apply_norm (U : E →ₗᵢ[ℝ] F) (x : F) :
    ‖isometryProjection U x‖ ≤ ‖x‖ :=
  ((isometryProjection U).le_opNorm x).trans
    ((mul_le_mul_of_nonneg_right (isometryProjection_norm U) (norm_nonneg x)).trans_eq (one_mul _))

theorem isometryProjection_map (U : E →ₗᵢ[ℝ] F) (v : E) : isometryProjection U (U v) = v := by
  have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U.toContinuousLinearMap).mp U.norm_map
  exact congrArg (fun L : E →L[ℝ] E => L v) h

def liftedHessian (U : E →ₗᵢ[ℝ] F) : (E →L[ℝ] E) →L[ℝ] (F →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ F E F U.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ F E E).flip (isometryProjection U))

@[simp] theorem liftedHessian_apply (U : E →ₗᵢ[ℝ] F) (H : E →L[ℝ] E) (x : F) :
    liftedHessian U H x = U (H (isometryProjection U x)) := rfl

theorem liftedHessian_norm (U : E →ₗᵢ[ℝ] F) (H : E →L[ℝ] E) : ‖liftedHessian U H‖ ≤ ‖H‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [liftedHessian_apply,U.norm_map]
  exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (isometryProjection_apply_norm U x) (norm_nonneg H))

theorem paddedLoss_gradient (U : E →ₗᵢ[ℝ] F) {f : E → ℝ} (hf : Differentiable ℝ f) :
    gradient (paddedLoss U f) = fun x => U (gradient f (isometryProjection U x)) := by
  funext x
  have hg := (hf (isometryProjection U x)).hasGradientAt
  have hh := hg.hasFDerivAt.comp x (isometryProjection U).hasFDerivAt
  have he : (InnerProductSpace.toDual ℝ E (gradient f (isometryProjection U x))).comp
      (isometryProjection U) =
      InnerProductSpace.toDual ℝ F (U (gradient f (isometryProjection U x))) := by
    ext v
    change ⟪gradient f (isometryProjection U x),isometryProjection U v⟫_ℝ =
      ⟪U (gradient f (isometryProjection U x)),v⟫_ℝ
    exact U.toContinuousLinearMap.adjoint_inner_right _ _
  rw [he] at hh
  exact (show HasGradientAt (paddedLoss U f) (U (gradient f (isometryProjection U x))) x from hh).gradient

theorem paddedLoss_hessian (U : E →ₗᵢ[ℝ] F) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : F) :
    fderiv ℝ (gradient (paddedLoss U f)) x =
      liftedHessian U (fderiv ℝ (gradient f) (isometryProjection U x)) := by
  rw [paddedLoss_gradient U (hf.differentiable (by norm_num))]
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  exact (U.toContinuousLinearMap.hasFDerivAt.comp x
    (((hg.differentiable (by norm_num)) (isometryProjection U x)).hasFDerivAt.comp x
      (isometryProjection U).hasFDerivAt)).fderiv

theorem paddedLoss_gradient_norm (U : E →ₗᵢ[ℝ] F) {f : E → ℝ} (hf : Differentiable ℝ f) (x : F) :
    ‖gradient (paddedLoss U f) x‖ = ‖gradient f (isometryProjection U x)‖ := by
  rw [paddedLoss_gradient U hf,U.norm_map]

theorem liftedHessian_quadratic (U : E →ₗᵢ[ℝ] F) (H : E →L[ℝ] E) (v : E) :
    ⟪liftedHessian U H (U v),U v⟫_ℝ = ⟪H v,v⟫_ℝ := by
  rw [liftedHessian_apply,isometryProjection_map,U.inner_map_map]

theorem paddedLoss_sosp_projects {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d)
    {f : Point m → ℝ} (hf : ContDiff ℝ 2 f) {ε γ : ℝ} {x : Point d}
    (hs : IsSOSP (paddedLoss U f) ε γ x) : IsSOSP f ε γ (isometryProjection U x) := by
  constructor
  · simpa only [paddedLoss_gradient_norm U (hf.differentiable (by norm_num))] using hs.1
  · intro v
    have hh := hs.2 (U v)
    change -γ*‖U v‖^2 ≤ ⟪fderiv ℝ (gradient (paddedLoss U f)) x (U v),U v⟫_ℝ at hh
    rwa [U.norm_map,paddedLoss_hessian U hf,liftedHessian_quadratic] at hh

end
end SampleReuse
