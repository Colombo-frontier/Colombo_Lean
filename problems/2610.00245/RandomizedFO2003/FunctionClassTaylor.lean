import RandomizedFO2003.OptimizationTaylor
import RandomizedFO2003.Model
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace RandomizedFO2003.Calculus

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Identify the actual gradient derivative with the symmetric second
Fréchet derivative via Riesz duality. -/
theorem hessian_pairing {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x u v : E) :
    inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x u) v = fderiv ℝ (fderiv ℝ f) x u v := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (gradient f) x =
      (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
    exact ((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x (hd x).hasFDerivAt).fderiv
  rw [he, ContinuousLinearMap.comp_apply]
  change ((toDual ℝ E) ((toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x u))) v = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem hessian_selfAdjoint {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    IsSelfAdjoint (fderiv ℝ (gradient f) x) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  change inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x u) v =
    inner (𝕜 := ℝ) u (fderiv ℝ (gradient f) x v)
  rw [hessian_pairing hf, real_inner_comm (fderiv ℝ (gradient f) x v) u, hessian_pairing hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)) u v

end RandomizedFO2003.Calculus

namespace RandomizedFO2003.Model

variable {d : ℕ} {f : Space d → ℝ} {Δ L₁ L₂ : ℝ}

theorem InFunctionClass.first_order_error_le (hf : InFunctionClass f Δ L₁ L₂) (x y : Space d) :
    |f y - f x - inner (𝕜 := ℝ) (gradient f x) (y - x)| ≤ L₁ / 2 * ‖y - x‖ ^ 2 :=
  Calculus.abs_first_order_error_le (hf.1.differentiable (by norm_num)) hf.2.2.1 x y

theorem InFunctionClass.gradient_error_le (hf : InFunctionClass f Δ L₁ L₂) (x y : Space d) :
    ‖gradient f y - gradient f x - fderiv ℝ (gradient f) x (y - x)‖ ≤ L₂ / 2 * ‖y - x‖ ^ 2 :=
  Calculus.norm_gradient_linearization_error_le hf.1 hf.2.2.2 x y

theorem InFunctionClass.quadratic_error_le (hf : InFunctionClass f Δ L₁ L₂) (x y : Space d) :
    |f y - f x - inner (𝕜 := ℝ) (gradient f x) (y - x) -
      (1 / 2) * inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x (y - x)) (y - x)| ≤
        L₂ / 6 * ‖y - x‖ ^ 3 :=
  Calculus.abs_quadratic_error_le hf.1 hf.2.2.2 x y

theorem InFunctionClass.hessian_norm_le (hf : InFunctionClass f Δ L₁ L₂) (hL₁ : 0 ≤ L₁) (x : Space d) :
    ‖fderiv ℝ (gradient f) x‖ ≤ L₁ :=
  norm_fderiv_le_of_lip' ℝ hL₁ (Filter.Eventually.of_forall (fun y => hf.2.2.1 y x))

theorem InFunctionClass.hessian_selfAdjoint (hf : InFunctionClass f Δ L₁ L₂) (x : Space d) :
    IsSelfAdjoint (fderiv ℝ (gradient f) x) := Calculus.hessian_selfAdjoint hf.1 x

end RandomizedFO2003.Model
