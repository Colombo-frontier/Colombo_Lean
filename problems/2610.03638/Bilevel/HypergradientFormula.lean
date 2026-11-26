import Bilevel.JointDerivative
import Bilevel.MixedDerivative
import Bilevel.ResponseDifferentiability
import Bilevel.HessianSymmetry
import Bilevel.CertifiedTilt

/-! The hypergradient and ideal frozen-tilt bias from the actual primitive model. -/
noncomputable section
namespace Bilevel.Model.Primitive
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem hasGradient_hyperobjective_with_inverse (r : P.Response) (x : X)
    (J : Y →L[ℝ] Y)
    (hleft : ∀ v, J (P.gyy x (r.y x) v) = v)
    (hright : ∀ v, P.gyy x (r.y x) (J v) = v) :
    HasGradientAt (P.hyperobjective r)
      (FrozenTilt.hypergradient (P.fx x (r.y x)) (P.gxy x (r.y x)) J (P.fy x (r.y x))) x := by
  let A := (P.gxy x (r.y x)).adjoint
  let R := -(J.comp A)
  have hr : HasFDerivAt r.y R x :=
    P.response_hasFDerivAt r x A J hleft (P.has_joint_gy x (r.y x))
  have h := Hypergradient.hasGradient_objective (fun p : X × Y => P.f p.1 p.2)
    r.y x (P.fx x (r.y x)) (P.fy x (r.y x)) R (P.has_joint_f x (r.y x)) hr
  have he := Hypergradient.hypergradient_formula A R J (P.fx x (r.y x))
    (P.fy x (r.y x)) (fun v => rfl)
  rw [he, P.inverse_adjoint_eq x (r.y x) J hright] at h
  simpa only [A, ContinuousLinearMap.adjoint_adjoint, hyperobjective,
    FrozenTilt.hypergradient] using h

variable [FiniteDimensional ℝ Y]

def inverseAt (x : X) (y : Y) : Y →L[ℝ] Y :=
  Classical.choose (P.hessian_inverse_exists x y)

theorem inverseAt_left (x : X) (y v : Y) : P.inverseAt x y (P.gyy x y v) = v :=
  (Classical.choose_spec (P.hessian_inverse_exists x y)).1 v

theorem inverseAt_right (x : X) (y v : Y) : P.gyy x y (P.inverseAt x y v) = v :=
  (Classical.choose_spec (P.hessian_inverse_exists x y)).2.1 v

theorem inverseAt_norm (x : X) (y : Y) : ‖P.inverseAt x y‖ ≤ μ⁻¹ :=
  (Classical.choose_spec (P.hessian_inverse_exists x y)).2.2

theorem hasGradient_hyperobjective (r : P.Response) (x : X) :
    HasGradientAt (P.hyperobjective r)
      (FrozenTilt.hypergradient (P.fx x (r.y x)) (P.gxy x (r.y x))
        (P.inverseAt x (r.y x)) (P.fy x (r.y x))) x :=
  P.hasGradient_hyperobjective_with_inverse r x (P.inverseAt x (r.y x))
    (P.inverseAt_left x (r.y x)) (P.inverseAt_right x (r.y x))

theorem gradient_hyperobjective (r : P.Response) (x : X) :
    gradient (P.hyperobjective r) x =
      FrozenTilt.hypergradient (P.fx x (r.y x)) (P.gxy x (r.y x))
        (P.inverseAt x (r.y x)) (P.fy x (r.y x)) :=
  (P.hasGradient_hyperobjective r x).gradient

/-- The manuscript's ideal bias inequality, for the actual gradient of the
actual composed objective, with all minimizers and inverses constructed. -/
theorem frozen_tilt_gradient_bias (r : P.Response) (x : X) {t : ℝ} (ht : 0 < t) :
    ‖FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x)
        (P.tiltedResponse x t (P.fy x (r.y x))) t - gradient (P.hyperobjective r) x‖ ≤
      ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t := by
  rw [P.gradient_hyperobjective r x]
  exact P.frozen_tilt_bias r x _ _ ht (P.tiltedResponse_stationary x t _)
    (P.inverseAt_left x (r.y x)) (P.inverseAt_right x (r.y x))

theorem frozen_tilt_gradient_exact (r : P.Response) (x : X) {t : ℝ}
    (ht : 0 < t) (hρ : ρ = 0) :
    FrozenTilt.estimator (P.fx x (r.y x)) (P.gx x) (r.y x)
      (P.tiltedResponse x t (P.fy x (r.y x))) t = gradient (P.hyperobjective r) x := by
  have h := P.frozen_tilt_gradient_bias r x ht
  have hc : ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t = 0 := by simp [hρ]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (h.trans_eq hc))

end Bilevel.Model.Primitive
