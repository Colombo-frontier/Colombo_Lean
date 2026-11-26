import SecondOrder.DimensionJets

namespace SecondOrder
noncomputable section

def curvatureJetConstant : ℝ := 15*completionDerivativeBound

theorem curvatureJetConstant_ge_one : 1 ≤ curvatureJetConstant := by
  norm_num [curvatureJetConstant, completionDerivativeBound]

variable {m : ℕ}

theorem periodicBlockPotential_dimensionJet (θ : BalancedVector m) (hm : 0 < m) (x : Point (2*m)) :
    DimensionJetBound curvatureJetConstant ((2*m:ℕ):ℝ) (periodicBlockPotential θ) x := by
  refine ⟨(periodicPotential_abs_le x θ).trans (by norm_num), ?_, ?_, ?_⟩
  · rw [norm_first_iteratedFDeriv]
    have hh := periodicBlockPotential_gradient_bound θ x
    simp only [gradient, LinearIsometryEquiv.norm_map] at hh
    exact hh.trans (div_le_div_of_nonneg_right curvatureJetConstant_ge_one (Real.sqrt_nonneg _))
  · rw [← norm_fderiv_gradient]
    exact (periodicBlockPotential_hessian_bound θ x).trans (div_le_div_of_nonneg_right
      (by norm_num [curvatureJetConstant, completionDerivativeBound]) (Nat.cast_nonneg _))
  · exact (periodicBlockPotential_third_bound θ hm x).trans (div_le_div_of_nonneg_right
      (by norm_num [curvatureJetConstant, completionDerivativeBound]) (Nat.cast_nonneg _))

theorem periodicCompletion_dimensionJet (θ : BalancedVector m) (hm : 0 < m) (x : Point (2*m)) :
    DimensionJetBound curvatureJetConstant ((2*m:ℕ):ℝ) (periodicCompletion θ) x := by
  refine ⟨?_, ?_, ?_, periodicCompletion_third_bound θ hm x⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (periodicCompletion_mem θ x).1]
    exact (periodicCompletion_mem θ x).2
  · rw [norm_first_iteratedFDeriv]
    have hh := periodicCompletion_gradient_bound θ x
    simp only [gradient, LinearIsometryEquiv.norm_map] at hh
    exact hh.trans (div_le_div_of_nonneg_right
      (by norm_num [curvatureJetConstant, completionDerivativeBound]) (Real.sqrt_nonneg _))
  · rw [← norm_fderiv_gradient]
    exact (periodicCompletion_hessian_coarse_bound θ x).trans (div_le_div_of_nonneg_right
      (by norm_num [curvatureJetConstant, completionDerivativeBound]) (Nat.cast_nonneg _))

end
end SecondOrder
