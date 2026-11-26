import SecondOrder.CurvatureLocal

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

/-- A fixed universal constant; no chain length or dimension enters its value. -/
def curvatureGeometryConstant : ℝ := 66*curvatureJetConstant^2

theorem curvatureGeometryConstant_pos : 0 < curvatureGeometryConstant := by
  norm_num [curvatureGeometryConstant, curvatureJetConstant, completionDerivativeBound]

theorem curvatureChain_second_third_bound (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (x : CurvatureSpace m T) :
    ‖fderiv ℝ (gradient (curvatureChain Θ)) x‖+‖iteratedFDeriv ℝ 3 (curvatureChain Θ) x‖ ≤
      curvatureGeometryConstant/((2*m:ℕ):ℝ) := by
  rw [norm_fderiv_gradient]
  have hh := add_le_add (curvatureChain_iterated_bound Θ hm 2 (Or.inl rfl) x)
    (curvatureChain_iterated_bound Θ hm 3 (Or.inr rfl) x)
  convert hh using 1 <;> unfold curvatureGeometryConstant <;> ring

theorem curvatureChain_gradient_lipschitz (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (x y : CurvatureSpace m T) :
    ‖gradient (curvatureChain Θ) y-gradient (curvatureChain Θ) x‖ ≤
      (33*curvatureJetConstant^2/((2*m:ℕ):ℝ))*‖y-x‖ :=
  gradient_lipschitz_of_second_bound
    ((curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))
    (curvatureChain_iterated_bound Θ hm 2 (Or.inl rfl)) x y

theorem curvatureChain_hessian_lipschitz (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (x y : CurvatureSpace m T) :
    ‖fderiv ℝ (gradient (curvatureChain Θ)) y-fderiv ℝ (gradient (curvatureChain Θ)) x‖ ≤
      (33*curvatureJetConstant^2/((2*m:ℕ):ℝ))*‖y-x‖ :=
  fderiv_gradient_lipschitz_of_third_bound (curvatureChain_contDiff Θ)
    (curvatureChain_iterated_bound Θ hm 3 (Or.inr rfl)) x y

/-- Every conclusion of the manuscript's capped-gate chain geometry lemma,
with T+1 blocks and genuine Euclidean derivatives throughout. -/
theorem curvatureChain_geometry (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (x : CurvatureSpace m T) :
    ContDiff ℝ 3 (curvatureChain Θ) ∧ curvatureChain Θ 0 = 0 ∧
    (-(T+1:ℕ) ≤ curvatureChain Θ x ∧ curvatureChain Θ x ≤ 0) ∧
    ‖fderiv ℝ (gradient (curvatureChain Θ)) x‖+‖iteratedFDeriv ℝ 3 (curvatureChain Θ) x‖ ≤
      curvatureGeometryConstant/((2*m:ℕ):ℝ) ∧
    ((∃ j, ‖periodicMean (x j) (Θ j)‖ ≤ 1/4) →
      ∃ v : CurvatureSpace m T, ‖v‖ = 1 ∧
        ⟪fderiv ℝ (gradient (curvatureChain Θ)) x v,v⟫_ℝ ≤ -1/(4*((2*m:ℕ):ℝ))) :=
  ⟨curvatureChain_contDiff Θ, curvatureChain_zero Θ, curvatureChain_range Θ x,
    curvatureChain_second_third_bound Θ hm x, curvatureChain_negative Θ hm x⟩

end
end SecondOrder
