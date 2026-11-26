import Bilevel.ModelBridge
import Bilevel.ResponseExistence

/-!
# An ideal frozen-tilt certificate with constructed responses

This assembles minimum attainment, inverse existence, and the analytic bias
bound. Comparison is to the explicit hypergradient expression. The stochastic
implementation and the full primitive-to-chain-rule identification are not
claimed by this theorem.
-/
noncomputable section
namespace Bilevel.Model.Primitive
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem ideal_tilt_certificate (x : X) {t : ℝ} (ht : 0 < t) :
    ∃ J : Y →L[ℝ] Y,
      (∀ v, J (P.gyy x (P.canonicalResponse.y x) v) = v) ∧
      (∀ v, P.gyy x (P.canonicalResponse.y x) (J v) = v) ∧
      ‖J‖ ≤ μ⁻¹ ∧
      ‖FrozenTilt.estimator (P.fx x (P.canonicalResponse.y x)) (P.gx x)
          (P.canonicalResponse.y x)
          (P.tiltedResponse x t (P.fy x (P.canonicalResponse.y x))) t -
        FrozenTilt.hypergradient (P.fx x (P.canonicalResponse.y x))
          (P.gxy x (P.canonicalResponse.y x)) J (P.fy x (P.canonicalResponse.y x))‖ ≤
        ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t := by
  obtain ⟨J, hl, hr, hn⟩ := P.hessian_inverse_exists x (P.canonicalResponse.y x)
  exact ⟨J, hl, hr, hn, P.frozen_tilt_bias P.canonicalResponse x _ J ht
    (P.tiltedResponse_stationary x t _) hl hr⟩

end Bilevel.Model.Primitive
