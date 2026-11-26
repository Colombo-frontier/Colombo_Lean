import Nonsmooth.HessianConvexity

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Primitive smoothness, coercivity, and derivative bounds. No marginal
law or integration closure is included among these fields. -/
structure C2StrongQuadraticPotential (U : E → ℝ) (ρ : ℝ) : Prop where
  smooth : ContDiff ℝ 2 U
  hessian_symmetric : ∀ z v w, fderiv ℝ (fderiv ℝ U) z v w = fderiv ℝ (fderiv ℝ U) z w v
  hessian_lower : ∀ z v, ρ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) z v v
  envelope : ∃ a B : ℝ, 0 < a ∧ 0 < B ∧ ∀ z,
    a * ‖z‖ ^ 2 - B ≤ U z ∧ U z ≤ B * (1 + ‖z‖ ^ 2)
  hessian_growth : ∃ D : ℝ, 0 ≤ D ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ U) z‖ ≤ D * (1 + ‖z‖ ^ 2)

theorem contDiff_two_derivative_data (U : E → ℝ) (hU : ContDiff ℝ 2 U) :
    (∀ z, HasFDerivAt U (fderiv ℝ U z) z) ∧
    (∀ z, HasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U) z) z) ∧
    Continuous (fderiv ℝ U) ∧ Continuous (fderiv ℝ (fderiv ℝ U)) := by
  have hS : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  exact ⟨fun z => (hU.differentiable (by norm_num) z).hasFDerivAt,
    fun z => (hS.differentiable (by norm_num) z).hasFDerivAt,
    hS.continuous, hS.continuous_fderiv (by norm_num)⟩

theorem c2StrongQuadraticPotential_strongConvex {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) : StrongConvexOn univ ρ U := by
  have hd := contDiff_two_derivative_data U hU.smooth
  exact strongConvexOn_of_hessian_lower U (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U))
    hd.1 hd.2.1 ρ hU.hessian_lower

theorem c2StrongQuadraticPotential_gradient_bound {U : E → ℝ} {ρ a B : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hb : ∀ z, a * ‖z‖ ^ 2 - B ≤ U z ∧ U z ≤ B * (1 + ‖z‖ ^ 2)) (z : E) :
    ‖fderiv ℝ U z‖ ≤ 6 * B * (1 + ‖z‖) := by
  have hc : ConvexOn ℝ univ U :=
    strongConvexOn_zero.mp ((c2StrongQuadraticPotential_strongConvex hU).mono hρ)
  apply convex_quadratic_gradient_bound U hc hB
  · intro y
    apply abs_le.mpr
    refine ⟨?_, (hb y).2⟩
    nlinarith [mul_nonneg ha (sq_nonneg ‖y‖), mul_nonneg hB (sq_nonneg ‖y‖), (hb y).1]
  · exact (hU.smooth.differentiable (by norm_num) z).hasFDerivAt

end
end Nonsmooth
