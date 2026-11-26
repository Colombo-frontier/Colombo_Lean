import SecondOrder.CompletionRegularity

namespace SecondOrder
noncomputable section

private theorem smul_difference_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s t : ℝ) (u v : F) {A B M N r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hs : |s| ≤ A) (hst : |s-t| ≤ B*r) (hv : ‖v‖ ≤ M) (huv : ‖u-v‖ ≤ N*r) :
    ‖s • u-t • v‖ ≤ (A*N+B*M)*r := by
  have he : s • u-t • v = s • (u-v)+(s-t) • v := by module
  rw [he]
  calc
    _ ≤ ‖s • (u-v)‖+‖(s-t) • v‖ := norm_add_le _ _
    _ = |s| *‖u-v‖+|s-t| *‖v‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ A*(N*r)+(B*r)*M := add_le_add
      (mul_le_mul hs huv (norm_nonneg _) hA)
      (mul_le_mul hst hv (norm_nonneg _) (mul_nonneg hB hr))
    _ = _ := by ring

variable {m : ℕ}

theorem periodicCompletion_gradient_bound (θ : BalancedVector m) (x : Point (2*m)) :
    ‖gradient (periodicCompletion θ) x‖ ≤ completionDerivativeBound/Real.sqrt ((2*m:ℕ):ℝ) := by
  rw [periodicCompletion_gradient, norm_smul]
  have hh := mul_le_mul (curvatureCompletion_derivative_bounds (periodicEnergy θ x)).1
    (periodicEnergy_gradient_bound θ x) (norm_nonneg _) (by norm_num [completionDerivativeBound])
  convert hh using 1 <;> ring

theorem periodicCompletion_hessian_coarse_bound (θ : BalancedVector m) (x : Point (2*m)) :
    ‖hessian (periodicCompletion θ) x‖ ≤ completionDerivativeBound/((2*m:ℕ):ℝ) := by
  apply (periodicCompletion_hessian_bound θ x).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_num [completionDerivativeBound]

theorem periodicEnergy_rankOne_bound (θ : BalancedVector m) (x : Point (2*m)) :
    ‖rankOneMap (gradient (periodicEnergy θ) x)‖ ≤ 1/((2*m:ℕ):ℝ) := by
  simpa only [rankOneMap, ContinuousLinearMap.norm_smulRight_apply, LinearIsometryEquiv.norm_map,
    ← pow_two, one_div] using periodicEnergy_gradient_sq_bound θ x

theorem periodicEnergy_rankOne_lipschitz (θ : BalancedVector m) (hm : 0 < m) (x y : Point (2*m)) :
    ‖rankOneMap (gradient (periodicEnergy θ) y)-rankOneMap (gradient (periodicEnergy θ) x)‖ ≤
      (4/((2*m:ℕ):ℝ))*‖y-x‖ := by
  apply (rankOneMap_sub_norm _ _).trans
  have hh := mul_le_mul (add_le_add (periodicEnergy_gradient_le_one θ hm y)
    (periodicEnergy_gradient_le_one θ hm x)) (periodicEnergy_gradient_lipschitz θ x y)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1+1)
  convert hh using 1 <;> ring

/-- The actual completed gate has a Hessian Lipschitz bound of universal size O(1/D). -/
theorem periodicCompletion_hessian_lipschitz (θ : BalancedVector m) (hm : 0 < m) (x y : Point (2*m)) :
    ‖hessian (periodicCompletion θ) y-hessian (periodicCompletion θ) x‖ ≤
      (15*completionDerivativeBound/((2*m:ℕ):ℝ))*‖y-x‖ := by
  have hC : 0 ≤ completionDerivativeBound := by norm_num [completionDerivativeBound]
  have hE := periodicEnergy_lipschitz θ hm x y
  have h1 : |deriv curvatureCompletion (periodicEnergy θ y)-deriv curvatureCompletion (periodicEnergy θ x)| ≤
      completionDerivativeBound*‖y-x‖ :=
    (curvatureCompletion_first_lipschitz _ _).trans (mul_le_mul_of_nonneg_left hE hC)
  have h2 : |deriv (deriv curvatureCompletion) (periodicEnergy θ y)-deriv (deriv curvatureCompletion) (periodicEnergy θ x)| ≤
      completionDerivativeBound*‖y-x‖ :=
    (curvatureCompletion_second_lipschitz _ _).trans (mul_le_mul_of_nonneg_left hE hC)
  have hH : ‖hessian (periodicEnergy θ) x‖ ≤ 2/((2*m:ℕ):ℝ) := by
    simpa only [periodicEnergy_hessian, norm_neg] using periodicBlockPotential_hessian_bound θ x
  have hs1 : |deriv curvatureCompletion (periodicEnergy θ y)| ≤ completionDerivativeBound :=
    (curvatureCompletion_derivative_bounds _).1
  have hs2 : |deriv (deriv curvatureCompletion) (periodicEnergy θ y)| ≤ completionDerivativeBound :=
    (curvatureCompletion_derivative_bounds _).2.1
  have ht1 := smul_difference_bound _ _ _ _ hC hC (norm_nonneg (y-x)) hs1 h1 hH
    (periodicEnergy_hessian_lipschitz θ hm x y)
  have ht2 := smul_difference_bound _ _ _ _ hC hC (norm_nonneg (y-x)) hs2 h2
    (periodicEnergy_rankOne_bound θ x) (periodicEnergy_rankOne_lipschitz θ hm x y)
  have he : hessian (periodicCompletion θ) y-hessian (periodicCompletion θ) x =
      (deriv curvatureCompletion (periodicEnergy θ y) • hessian (periodicEnergy θ) y-
        deriv curvatureCompletion (periodicEnergy θ x) • hessian (periodicEnergy θ) x)+
      (deriv (deriv curvatureCompletion) (periodicEnergy θ y) • rankOneMap (gradient (periodicEnergy θ) y)-
        deriv (deriv curvatureCompletion) (periodicEnergy θ x) • rankOneMap (gradient (periodicEnergy θ) x)) := by
    rw [periodicCompletion_hessian, periodicCompletion_hessian]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hh := add_le_add ht1 ht2
  convert hh using 1 <;> ring

theorem periodicCompletion_third_bound (θ : BalancedVector m) (hm : 0 < m) (x : Point (2*m)) :
    ‖iteratedFDeriv ℝ 3 (periodicCompletion θ) x‖ ≤ 15*completionDerivativeBound/((2*m:ℕ):ℝ) := by
  rw [norm_third_eq_norm_fderiv_hessian]
  apply norm_fderiv_le_of_lip' ℝ (by unfold completionDerivativeBound; positivity)
  exact Filter.Eventually.of_forall (fun y => periodicCompletion_hessian_lipschitz θ hm x y)

end
end SecondOrder
