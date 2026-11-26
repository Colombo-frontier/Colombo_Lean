import GradientHessian.NalenTaylor
import GradientHessian.Model
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The NALEN vector gradient and Hessian are the actual derivatives of
the objective. Riesz transport preserves the Hessian Lipschitz constant;
symmetry follows from C2 regularity. -/

noncomputable section
namespace GradientHessian.Nalen
open InnerProductSpace
open scoped InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def hessianOperator (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x)

@[simp] theorem hessianOperator_inner (f : E → ℝ) (x u v : E) :
    ⟪hessianOperator f x u,v⟫_ℝ = fderiv ℝ (fderiv ℝ f) x u v :=
  toDual_symm_apply

theorem hessianOperator_symmetric {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x u v : E) :
    ⟪hessianOperator f x u,v⟫_ℝ=⟪u,hessianOperator f x v⟫_ℝ := by
  rw [real_inner_comm (hessianOperator f x v) u,hessianOperator_inner,hessianOperator_inner]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v

theorem gradient_hasFDerivAt {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    HasFDerivAt (gradient f) (hessianOperator f x) x := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    ((hd.differentiable (by norm_num)) x).hasFDerivAt

theorem gradient_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    fderiv ℝ (gradient f) x=hessianOperator f x :=
  (gradient_hasFDerivAt hf x).fderiv

theorem hessianOperator_sub_norm_le (f : E → ℝ) (x y : E) :
    ‖hessianOperator f x-hessianOperator f y‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ := by
  apply (hessianOperator f x-hessianOperator f y).opNorm_le_bound
    (norm_nonneg (fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y))
  intro u
  have he : (hessianOperator f x-hessianOperator f y) u =
      (toDual ℝ E).symm ((fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y) u) := by
    simp [hessianOperator,map_sub]
  rw [he,(toDual ℝ E).symm.norm_map]
  exact ContinuousLinearMap.le_opNorm _ u

theorem hessianOperator_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ f))) : LipschitzWith L (hessianOperator f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  exact (hessianOperator_sub_norm_le f x y).trans
    (by simpa only [dist_eq_norm] using hL.dist_le_mul x y)

theorem gradient_derivative_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ f))) :
    LipschitzWith L (fderiv ℝ (gradient f)) := by
  have he : fderiv ℝ (gradient f)=hessianOperator f := funext (gradient_fderiv hf)
  rw [he]
  exact hessianOperator_lipschitz hL

theorem gradient_taylor {f : E → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ f))) (x y : E) :
    ‖gradient f y-gradient f x-hessianOperator f x (y-x)‖ ≤ (L : ℝ)*‖y-x‖^2 := by
  simpa only [gradient_fderiv hf] using first_taylor_remainder
    (fun z => (gradient_hasFDerivAt hf z).differentiableAt)
    (gradient_derivative_lipschitz hf hL) x y

theorem objective_prediction_remainder {f : E → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ f)))
    (B : E →L[ℝ] E) (z y snapshot : E) {δ : ℝ}
    (hB : ‖B-hessianOperator f snapshot‖ ≤ δ) :
    ‖gradient f z+B (y-z)-gradient f y‖ ≤
      ((L : ℝ)*‖y-z‖+(L : ℝ)*‖snapshot-z‖+δ)*‖y-z‖ := by
  exact lazy_prediction_remainder
    (fun x => (gradient_hasFDerivAt hf x).differentiableAt)
    (gradient_derivative_lipschitz hf hL) B z y snapshot
    (by simpa only [gradient_fderiv hf] using hB)

end GradientHessian.Nalen
