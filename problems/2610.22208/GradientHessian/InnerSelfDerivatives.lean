import GradientHessian.InnerDisjointDerivatives
import GradientHessian.InnerActivation

/-! The task residual part of the inner construction has a square-root
gradient bound and dimension-free Hessian and third derivative bounds. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem taskResidual_contDiff (v : Fin (k + 2) → E) :
    ContDiff ℝ 3 (LatchChain.residual (k + 1) v (radius k)) := by
  apply (LatchChain.self_contDiff (k + 1) v (radius k) 0).sub
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 2) => E) j).contDiff.norm_sq ℝ)

variable [CompleteSpace E]

theorem sumResidual_first_derivative_bound (v : Fin m → Fin (k + 2) → E)
    (hv : ∀ i j, ‖v i j‖ = 1) (Z : Space Y E m (k + 2)) :
    ‖iteratedFDeriv ℝ 1 (sumResidual v) Z‖ ≤
      (LatchLemma.latchConstant * Real.sqrt (k + 2)) * Real.sqrt m := by
  apply disjointSum_first_derivative_bound
    (fun i => LatchChain.residual (k + 1) (v i) (radius k))
    (fun i => taskResidual_contDiff (v i))
    (mul_nonneg LatchLemma.latchConstant_pos.le (Real.sqrt_nonneg _))
  intro i U
  exact (LatchLemma.latch_bounds k (v i) (by norm_num : (1 : ℝ) ≤ 1) (hv i)).residual_first U

theorem sumResidual_second_derivative_bound (v : Fin m → Fin (k + 2) → E)
    (hv : ∀ i j, ‖v i j‖ = 1) (Z : Space Y E m (k + 2)) :
    ‖iteratedFDeriv ℝ 2 (sumResidual v) Z‖ ≤ LatchLemma.latchConstant := by
  apply disjointSum_higher_derivative_bound
    (fun i => LatchChain.residual (k + 1) (v i) (radius k))
    (fun i => taskResidual_contDiff (v i)) LatchLemma.latchConstant_pos.le
    (by norm_num) (by norm_num)
  intro i U
  simpa using (LatchLemma.latch_bounds k (v i) (by norm_num : (1 : ℝ) ≤ 1) (hv i)).residual_second U

theorem sumResidual_third_derivative_bound (v : Fin m → Fin (k + 2) → E)
    (hv : ∀ i j, ‖v i j‖ = 1) (Z : Space Y E m (k + 2)) :
    ‖iteratedFDeriv ℝ 3 (sumResidual v) Z‖ ≤ LatchLemma.latchConstant := by
  apply disjointSum_higher_derivative_bound
    (fun i => LatchChain.residual (k + 1) (v i) (radius k))
    (fun i => taskResidual_contDiff (v i)) LatchLemma.latchConstant_pos.le
    (by norm_num) (by norm_num)
  intro i U
  simpa using (LatchLemma.latch_bounds k (v i) (by norm_num : (1 : ℝ) ≤ 1) (hv i)).residual_third U

def selfGradientConstant : ℝ := LatchLemma.latchConstant * Real.sqrt (absoluteDepth + 2)

theorem selfGradientConstant_pos : 0 < selfGradientConstant := by
  unfold selfGradientConstant
  exact mul_pos LatchLemma.latchConstant_pos (Real.sqrt_pos.mpr (by norm_num [absoluteDepth]))

theorem absolute_sumResidual_derivative_bounds
    (v : Fin m → Fin (absoluteDepth + 2) → E) (hv : ∀ i j, ‖v i j‖ = 1)
    (Z : Space Y E m (absoluteDepth + 2)) :
    ‖iteratedFDeriv ℝ 1 (sumResidual v) Z‖ ≤ selfGradientConstant * Real.sqrt m ∧
    ‖iteratedFDeriv ℝ 2 (sumResidual v) Z‖ + ‖iteratedFDeriv ℝ 3 (sumResidual v) Z‖ ≤
      2 * LatchLemma.latchConstant := by
  refine ⟨sumResidual_first_derivative_bound v hv Z, ?_⟩
  linarith [sumResidual_second_derivative_bound v hv Z, sumResidual_third_derivative_bound v hv Z]

end GradientHessian.Inner
