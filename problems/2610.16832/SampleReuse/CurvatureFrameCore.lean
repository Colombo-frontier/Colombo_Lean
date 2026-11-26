import SampleReuse.CurvatureGradientBound
import SampleReuse.CurvatureNegative
import SecondOrder.ScalarLinearScaling
import SecondOrder.ScaledCurvatureCompletion
import Mathlib.Analysis.InnerProductSpace.Adjoint

open SecondOrder
open scoped InnerProductSpace

namespace SampleReuse
noncomputable section

variable {d T : ℕ}

def curvatureFrameProjection (U : Point (T+1) →ₗᵢ[ℝ] Point d) :
    Point d →L[ℝ] Point (T+1) := U.toContinuousLinearMap.adjoint

theorem curvatureFrameProjection_norm (U : Point (T+1) →ₗᵢ[ℝ] Point d) :
    ‖curvatureFrameProjection U‖ ≤ 1 := by
  unfold curvatureFrameProjection
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using (U.norm_map x).le

theorem curvatureFrameProjection_map (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    (v : Point (T+1)) : curvatureFrameProjection U (U v) = v := by
  have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U.toContinuousLinearMap).mp U.norm_map
  exact congrArg (fun L : Point (T+1) →L[ℝ] Point (T+1) => L v) h

def curvatureFrameMap (U : Point (T+1) →ₗᵢ[ℝ] Point d) (β : ℝ) :
    Point d →L[ℝ] Point (T+1) := β • curvatureFrameProjection U

theorem curvatureFrameMap_norm (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {β : ℝ} (hβ : 0 ≤ β) : ‖curvatureFrameMap U β‖ ≤ β := by
  rw [curvatureFrameMap, norm_smul β (curvatureFrameProjection U), Real.norm_of_nonneg hβ]
  exact (mul_le_mul_of_nonneg_left (curvatureFrameProjection_norm U) hβ).trans_eq (mul_one β)

def curvatureFrameCore (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β : ℝ) : Point d → ℝ :=
  scalarLinearScaling (deterministicCurvatureChain T) A (curvatureFrameMap U β)

theorem curvatureFrameCore_contDiff (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    (A β : ℝ) (n : ℕ∞) : ContDiff ℝ n (curvatureFrameCore U A β) :=
  scalarLinearScaling_contDiff (deterministicCurvatureChain_contDiff T n) A _

theorem curvatureFrameCore_zero (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β : ℝ) :
    curvatureFrameCore U A β 0 = 0 := by
  simp [curvatureFrameCore, scalarLinearScaling, deterministicCurvatureChain_zero]

theorem curvatureFrameCore_range (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {A : ℝ} (hA : 0 ≤ A) (β : ℝ) (x : Point d) :
    -4*A*(T+1:ℕ) ≤ curvatureFrameCore U A β x ∧ curvatureFrameCore U A β x ≤ 0 := by
  have hh := deterministicCurvatureChain_range T (curvatureFrameMap U β x)
  constructor
  · have hm := mul_le_mul_of_nonneg_left hh.1 hA
    simpa only [curvatureFrameCore, scalarLinearScaling] using (show
      -4*A*(T+1:ℕ) ≤ A*deterministicCurvatureChain T (curvatureFrameMap U β x) by nlinarith only [hm])
  · exact mul_nonpos_of_nonneg_of_nonpos hA hh.2

theorem curvatureFrameCore_iterated_bound (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β) (k : ℕ) (hk : k=2 ∨ k=3) (x : Point d) :
    ‖iteratedFDeriv ℝ k (curvatureFrameCore U A β) x‖ ≤
      A*β^k*(17*curvatureScalarConstant^2) :=
  scalarLinearScaling_iterated_bound_of_le _ hA hβ (by positivity) _
    (curvatureFrameMap_norm U hβ) k (deterministicCurvatureChain_contDiff T k) x
    (deterministicCurvatureChain_iterated_bound T k hk _)

theorem curvatureFrameCore_gradient_bound (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β) (x : Point d) :
    ‖gradient (curvatureFrameCore U A β) x‖ ≤
      A*β*(17*curvatureScalarConstant^2*Real.sqrt (T+1:ℕ)) := by
  have hh := scalarLinearScaling_gradient_bound (deterministicCurvatureChain_contDiff T 2)
    A (curvatureFrameMap U β) x
  rw [abs_of_nonneg hA] at hh
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (curvatureFrameMap_norm U hβ) hA)
    (deterministicCurvatureChain_gradient_bound T _)
    (norm_nonneg _) (mul_nonneg hA hβ))

theorem curvatureFrameCore_hessian_bound (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β) (x : Point d) :
    ‖hessian (curvatureFrameCore U A β) x‖ ≤ A*β^2*(17*curvatureScalarConstant^2) := by
  change ‖fderiv ℝ (gradient (curvatureFrameCore U A β)) x‖ ≤ _
  rw [norm_fderiv_gradient]
  exact curvatureFrameCore_iterated_bound U hA hβ 2 (Or.inl rfl) x

theorem curvatureFrameCore_hessian_lipschitz (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β) (x y : Point d) :
    ‖hessian (curvatureFrameCore U A β) y-hessian (curvatureFrameCore U A β) x‖ ≤
      A*β^3*(17*curvatureScalarConstant^2)*‖y-x‖ :=
  fderiv_gradient_lipschitz_of_third_bound (curvatureFrameCore_contDiff U A β 3)
    (fun z => curvatureFrameCore_iterated_bound U hA hβ 3 (Or.inr rfl) z) x y

theorem curvatureFrameCore_quadratic (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    (A β : ℝ) (x : Point d) (v : Point (T+1)) :
    secondQuadratic (curvatureFrameCore U A β) x (U v) =
      A*β^2*secondQuadratic (deterministicCurvatureChain T) (curvatureFrameMap U β x) v := by
  have hf := deterministicCurvatureChain_contDiff T 2
  unfold curvatureFrameCore scalarLinearScaling
  change secondQuadratic (fun y => A*(deterministicCurvatureChain T ∘ curvatureFrameMap U β) y) x (U v) = _
  rw [secondQuadratic_const_mul (hf.comp (curvatureFrameMap U β).contDiff)]
  change A*secondQuadratic (deterministicCurvatureChain T ∘ curvatureFrameMap U β) x (U v) = _
  rw [secondQuadratic_comp_linear hf]
  simp only [curvatureFrameMap, ContinuousLinearMap.smul_apply, curvatureFrameProjection_map]
  rw [secondQuadratic_smul]
  ring

theorem curvatureFrameCore_frontier (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {A : ℝ} (hA : 0 ≤ A) (β : ℝ) (x : Point d) (j : Fin (T+1))
    (hj : |curvatureFrameMap U β x j| ≤ 1)
    (hprior : ∀ i : Fin (T+1), i < j → 1 < |curvatureFrameMap U β x i|) :
    ‖U (blockUnit j (1:ℝ))‖ = 1 ∧
      ⟪hessian (curvatureFrameCore U A β) x (U (blockUnit j (1:ℝ))),U (blockUnit j (1:ℝ))⟫_ℝ ≤
        -(A*β^2*Real.exp (-(9:ℝ)/4)) := by
  refine ⟨by simp only [U.norm_map, blockUnit_norm, norm_one], ?_⟩
  change ⟪fderiv ℝ (gradient (curvatureFrameCore U A β)) x
    (U (blockUnit j (1:ℝ))),U (blockUnit j (1:ℝ))⟫_ℝ ≤ _
  rw [← secondQuadratic_eq_inner (curvatureFrameCore_contDiff U A β 2), curvatureFrameCore_quadratic]
  have hh := mul_le_mul_of_nonneg_left
    (deterministicCurvatureChain_frontier T (curvatureFrameMap U β x) j hj hprior)
    (mul_nonneg hA (sq_nonneg β))
  simpa only [mul_neg] using hh

end
end SampleReuse
