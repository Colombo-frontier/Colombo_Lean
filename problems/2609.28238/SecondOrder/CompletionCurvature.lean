import SecondOrder.PeriodicCompletion
import SecondOrder.DirectionalCurvature

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section
variable {m : ℕ}

theorem periodicCompletion_secondQuadratic (θ : BalancedVector m) (x v : Point (2*m)) :
    secondQuadratic (periodicCompletion θ) x v =
      -deriv curvatureCompletion (periodicEnergy θ x)*secondQuadratic (periodicBlockPotential θ) x v+
      deriv (deriv curvatureCompletion) (periodicEnergy θ x)*⟪gradient (periodicEnergy θ) x,v⟫_ℝ^2 := by
  rw [secondQuadratic_eq_inner ((periodicCompletion_contDiff θ).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)),
    secondQuadratic_eq_inner (periodicBlockPotential_contDiff θ 2)]
  change ⟪hessian (periodicCompletion θ) x v,v⟫_ℝ = _
  rw [periodicCompletion_hessian, periodicEnergy_hessian]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, inner_add_left, inner_smul_left, inner_neg_left,
    RCLike.conj_to_real, rankOneMap, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply]
  simp only [hessian]
  ring

/-- At an unfinished block, the outgoing gate has nonnegative curvature along
any nonpositive-curvature direction of the periodic potential. -/
theorem periodicCompletion_nonneg_curvature (θ : BalancedVector m) (x v : Point (2*m))
    (hx : ‖periodicMean x θ‖ ≤ 1/4)
    (hv : secondQuadratic (periodicBlockPotential θ) x v ≤ 0) :
    0 ≤ secondQuadratic (periodicCompletion θ) x v := by
  rw [periodicCompletion_secondQuadratic]
  have hb := curvatureCompletion_derivatives_nonneg (periodicEnergy_unfinished θ x hx)
  exact add_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hb.1) hv)
    (mul_nonneg hb.2 (sq_nonneg _))

end
end SecondOrder
