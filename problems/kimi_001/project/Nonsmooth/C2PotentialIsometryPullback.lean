import Nonsmooth.C2StrongQuadraticPotential
import Nonsmooth.OrthogonalCoordinateBounds
import Nonsmooth.OrthogonalCoordinateCurvature

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem c2_potential_isometry_derivatives (U : E → ℝ) (hU : ContDiff ℝ 2 U)
    (L : F →ₗᵢ[ℝ] E) :
    (∀ t, fderiv ℝ (fun r => U (L r)) t =
      coordinateScore (fderiv ℝ U) L.toContinuousLinearMap 0 t 0) ∧
    (∀ t, fderiv ℝ (fderiv ℝ (fun r => U (L r))) t =
      coordinateHessian (fderiv ℝ (fderiv ℝ U)) L.toContinuousLinearMap 0 t 0) := by
  have hd := contDiff_two_derivative_data U hU
  have hfirst (t : F) : HasFDerivAt (fun r => U (L r))
      (coordinateScore (fderiv ℝ U) L.toContinuousLinearMap 0 t 0) t := by
    simpa only [coordinatePotential, coordinatePoint, smul_zero, add_zero,
      LinearIsometry.coe_toContinuousLinearMap] using
      coordinatePotential_hasFDerivAt U (fderiv ℝ U) hd.1 L.toContinuousLinearMap 0 t 0
  have hf : fderiv ℝ (fun r => U (L r)) =
      fun t => coordinateScore (fderiv ℝ U) L.toContinuousLinearMap 0 t 0 :=
    funext (fun t => (hfirst t).fderiv)
  refine ⟨fun t => (hfirst t).fderiv, ?_⟩
  intro t
  rw [hf]
  exact (coordinateScore_hasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U))
    hd.2.1 L.toContinuousLinearMap 0 t 0).fderiv

theorem c2StrongQuadraticPotential_isometry_pullback {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (L : F →ₗᵢ[ℝ] E) :
    C2StrongQuadraticPotential (fun t => U (L t)) ρ := by
  have hd := (c2_potential_isometry_derivatives U hU.smooth L).2
  refine ⟨hU.smooth.comp L.toContinuousLinearMap.contDiff, ?_, ?_, ?_, ?_⟩
  · intro t v w
    rw [hd]
    exact coordinateHessian_symmetric (fderiv ℝ (fderiv ℝ U)) hU.hessian_symmetric
      L.toContinuousLinearMap 0 t 0 v w
  · intro t v
    rw [hd]
    have h := hU.hessian_lower (L t) (L v)
    simpa only [coordinateHessian, coordinatePrecompose, coordinatePoint,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, smul_zero, add_zero,
      LinearIsometry.coe_toContinuousLinearMap, L.norm_map] using h
  · obtain ⟨a, B, ha, hB, hb⟩ := hU.envelope
    exact ⟨a, B, ha, hB, fun t => by simpa only [L.norm_map] using hb (L t)⟩
  · obtain ⟨D, hD, hb⟩ := hU.hessian_growth
    refine ⟨D, hD, fun t => ?_⟩
    rw [hd]
    have hn := coordinateHessian_norm_le (fderiv ℝ (fderiv ℝ U))
      L.toContinuousLinearMap L.norm_toContinuousLinearMap_le 0 t 0
    apply hn.trans
    simpa only [coordinatePoint, smul_zero, add_zero,
      LinearIsometry.coe_toContinuousLinearMap, L.norm_map] using hb (L t)

end
end Nonsmooth
