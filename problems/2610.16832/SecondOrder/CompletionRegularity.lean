import SecondOrder.PeriodicCompletion

namespace SecondOrder
noncomputable section

/-- One explicit universal bound for the first three scalar completion derivatives. -/
def completionDerivativeBound : ℝ := 100000000

theorem curvatureCompletion_derivative_bounds (x : ℝ) :
    ‖deriv curvatureCompletion x‖ ≤ completionDerivativeBound ∧
    ‖deriv (deriv curvatureCompletion) x‖ ≤ completionDerivativeBound ∧
    ‖deriv (deriv (deriv curvatureCompletion)) x‖ ≤ completionDerivativeBound := by
  rw [curvatureCompletion, deriv_affineGate, deriv_affineGateFirst, deriv_affineGateSecond]
  refine ⟨(affineGateFirst_bound (64/3) (1/128) x).trans (by
      rw [abs_of_nonneg (show (0:ℝ) ≤ 64/3 by norm_num)]
      norm_num [completionDerivativeBound]),
    (affineGateSecond_bound (64/3) (1/128) x).trans (by norm_num [completionDerivativeBound]), ?_⟩
  have hh := (gate_derivative_bounds ((64/3)*(x-1/128))).2.2
  rw [deriv_gate, deriv_gateFirst, deriv_gateSecond] at hh
  have he : ‖affineGateThird (64/3) (1/128) x‖ = (64/3:ℝ)^3*‖gateThird ((64/3)*(x-1/128))‖ := by
    rw [affineGateThird, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (64/3:ℝ)^3)
  exact hm.trans (by norm_num [completionDerivativeBound])

theorem curvatureCompletion_first_lipschitz (x y : ℝ) :
    |deriv curvatureCompletion y-deriv curvatureCompletion x| ≤ completionDerivativeBound*|y-x| := by
  have hd (z : ℝ) : HasDerivAt (deriv curvatureCompletion) (deriv (deriv curvatureCompletion) z) z := by
    rw [curvatureCompletion, deriv_affineGate, deriv_affineGateFirst]
    exact affineGateFirst_hasDerivAt _ _ _
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Set.univ) => (hd z).hasDerivWithinAt)
    (fun z _ => (curvatureCompletion_derivative_bounds z).2.1)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ x) (Set.mem_univ y)

theorem curvatureCompletion_second_lipschitz (x y : ℝ) :
    |deriv (deriv curvatureCompletion) y-deriv (deriv curvatureCompletion) x| ≤ completionDerivativeBound*|y-x| := by
  have hd (z : ℝ) : HasDerivAt (deriv (deriv curvatureCompletion))
      (deriv (deriv (deriv curvatureCompletion)) z) z := by
    rw [curvatureCompletion, deriv_affineGate, deriv_affineGateFirst, deriv_affineGateSecond]
    exact affineGateSecond_hasDerivAt _ _ _
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Set.univ) => (hd z).hasDerivWithinAt)
    (fun z _ => (curvatureCompletion_derivative_bounds z).2.2)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ x) (Set.mem_univ y)

variable {m : ℕ}

theorem periodicEnergy_gradient_bound (θ : BalancedVector m) (x : Point (2*m)) :
    ‖gradient (periodicEnergy θ) x‖ ≤ 1/Real.sqrt ((2*m:ℕ):ℝ) := by
  simpa only [periodicEnergy_gradient, norm_neg] using periodicBlockPotential_gradient_bound θ x

theorem periodicEnergy_gradient_le_one (θ : BalancedVector m) (hm : 0 < m) (x : Point (2*m)) :
    ‖gradient (periodicEnergy θ) x‖ ≤ 1 := by
  have hD : (1:ℝ) ≤ (2*m:ℕ) := by exact_mod_cast (by omega : 1 ≤ 2*m)
  have hh := (periodicEnergy_gradient_sq_bound θ x).trans (inv_le_one_of_one_le₀ hD)
  nlinarith [norm_nonneg (gradient (periodicEnergy θ) x)]

theorem periodicEnergy_lipschitz (θ : BalancedVector m) (hm : 0 < m) (x y : Point (2*m)) :
    |periodicEnergy θ y-periodicEnergy θ x| ≤ ‖y-x‖ := by
  have hd (z : Point (2*m)) : ‖fderiv ℝ (periodicEnergy θ) z‖ ≤ 1 := by
    have hh := periodicEnergy_gradient_le_one θ hm z
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hh
  simpa only [Real.norm_eq_abs, one_mul] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => (periodicEnergy_contDiff θ 1).differentiable (by norm_num) z)
    (fun z _ => hd z) (convex_univ : Convex ℝ (Set.univ : Set (Point (2*m))))
    (Set.mem_univ x) (Set.mem_univ y)

theorem periodicEnergy_gradient_lipschitz (θ : BalancedVector m) (x y : Point (2*m)) :
    ‖gradient (periodicEnergy θ) y-gradient (periodicEnergy θ) x‖ ≤ (2/((2*m:ℕ):ℝ))*‖y-x‖ := by
  apply gradient_lipschitz_of_second_bound (periodicEnergy_contDiff θ 2)
  intro z
  rw [← norm_fderiv_gradient]
  change ‖hessian (periodicEnergy θ) z‖ ≤ _
  simpa only [periodicEnergy_hessian, norm_neg] using periodicBlockPotential_hessian_bound θ z

theorem periodicEnergy_hessian_lipschitz (θ : BalancedVector m) (hm : 0 < m) (x y : Point (2*m)) :
    ‖hessian (periodicEnergy θ) y-hessian (periodicEnergy θ) x‖ ≤ (8/((2*m:ℕ):ℝ))*‖y-x‖ := by
  rw [periodicEnergy_hessian, periodicEnergy_hessian]
  have he : -hessian (periodicBlockPotential θ) y-(-hessian (periodicBlockPotential θ) x) =
      -(hessian (periodicBlockPotential θ) y-hessian (periodicBlockPotential θ) x) := by abel
  rw [he, norm_neg]
  exact periodicBlockPotential_hessian_lipschitz θ hm x y

end
end SecondOrder
