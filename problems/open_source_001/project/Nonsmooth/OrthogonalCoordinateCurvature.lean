import Nonsmooth.OrthogonalCoordinateBounds

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem orthogonal_coordinate_hessian_block (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (L : F →ₗᵢ[ℝ] E) (u : E) (hu : ‖u‖ = 1)
    (ho : ∀ t, inner ℝ (L t) u = (0 : ℝ)) (ρ : ℝ)
    (hsym : ∀ z v w, H z v w = H z w v)
    (hl : ∀ z v, ρ * ‖v‖ ^ 2 ≤ H z v v) (t : F) (x : ℝ) (v : F) (p : ℝ) :
    ρ * (p ^ 2 + ‖v‖ ^ 2) ≤
      H (coordinatePoint L.toContinuousLinearMap u t x) u u * p ^ 2 +
      2 * coordinatePrecompose L.toContinuousLinearMap
        (H (coordinatePoint L.toContinuousLinearMap u t x) u) v * p +
      coordinateHessian H L.toContinuousLinearMap u t x v v := by
  let z := coordinatePoint L.toContinuousLinearMap u t x
  have hb := hl z (coordinatePoint L.toContinuousLinearMap u v p)
  rw [orthogonal_coordinate_norm_sq L u hu ho v p] at hb
  change ρ * (‖v‖ ^ 2 + p ^ 2) ≤ H z (L v + p • u) (L v + p • u) at hb
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, hsym z (L v) u] at hb
  change ρ * (p ^ 2 + ‖v‖ ^ 2) ≤ H z u u * p ^ 2 + 2 * H z u (L v) * p + H z (L v) (L v)
  nlinarith

theorem coordinateHessian_symmetric (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ z v w, H z v w = H z w v)
    (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) (v w : F) :
    coordinateHessian H L u t x v w = coordinateHessian H L u t x w v :=
  hsym (coordinatePoint L u t x) (L v) (L w)

end
end Nonsmooth
