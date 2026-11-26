import SecondOrder.ScaledCurvatureLoss

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

theorem scaledCurvaturePopulation_zero (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) :
    scaledCurvaturePopulation Θ A β 0=0 := by
  simp [scaledCurvaturePopulation, scalarLinearScaling, curvatureChain_zero]

theorem scaledCurvaturePopulation_gap (Θ : Fin (T+1) → BalancedVector m)
    {A : ℝ} (hA : 0≤A) (β : ℝ) (x : Point (CurvatureDimension m T)) :
    scaledCurvaturePopulation Θ A β 0-scaledCurvaturePopulation Θ A β x ≤ A*(T+1:ℕ) := by
  rw [scaledCurvaturePopulation_zero]
  have hh := mul_le_mul_of_nonneg_left (curvatureChain_range Θ (curvatureDilation m T β x)).1 hA
  change 0-A*curvatureChain Θ (curvatureDilation m T β x) ≤ _
  linarith only [hh]

theorem scaledCurvaturePopulation_derivative_bounds (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (x : Point (CurvatureDimension m T)) :
    ‖hessian (scaledCurvaturePopulation Θ A β) x‖≤A*β^2*(curvatureGeometryConstant/((2*m:ℕ):ℝ)) ∧
    ‖iteratedFDeriv ℝ 3 (scaledCurvaturePopulation Θ A β) x‖≤
      A*β^3*(curvatureGeometryConstant/((2*m:ℕ):ℝ)) := by
  let L := curvatureDilation m T β
  have hL : ‖L‖≤β := by simpa only [abs_of_nonneg hβ] using curvatureDilation_norm m T β
  have hh := curvatureChain_second_third_bound Θ hm (L x)
  have h2 : ‖iteratedFDeriv ℝ 2 (curvatureChain Θ) (L x)‖≤curvatureGeometryConstant/((2*m:ℕ):ℝ) := by
    rw [← norm_fderiv_gradient]
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans hh
  have h3 : ‖iteratedFDeriv ℝ 3 (curvatureChain Θ) (L x)‖≤curvatureGeometryConstant/((2*m:ℕ):ℝ) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans hh
  have hM : 0≤curvatureGeometryConstant/((2*m:ℕ):ℝ) :=
    div_nonneg curvatureGeometryConstant_pos.le (Nat.cast_nonneg _)
  constructor
  · rw [hessian, norm_fderiv_gradient]
    exact scalarLinearScaling_iterated_bound_of_le _ hA hβ hM L hL 2
      ((curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)) x h2
  · exact scalarLinearScaling_iterated_bound_of_le _ hA hβ hM L hL 3 (curvatureChain_contDiff Θ) x h3

theorem scaledCurvaturePopulation_gradient_lipschitz (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (x y : Point (CurvatureDimension m T)) :
    ‖gradient (scaledCurvaturePopulation Θ A β) x-gradient (scaledCurvaturePopulation Θ A β) y‖≤
      (A*β^2*(curvatureGeometryConstant/((2*m:ℕ):ℝ)))*‖x-y‖ := by
  apply gradient_lipschitz_of_second_bound
    ((scaledCurvaturePopulation_contDiff Θ A β).of_le (show (2:WithTop ℕ∞)≤3 by decide)) _ y x
  intro z
  simpa only [hessian, norm_fderiv_gradient] using
    (scaledCurvaturePopulation_derivative_bounds Θ hm hA hβ z).1

theorem scaledCurvaturePopulation_hessian_lipschitz (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (x y : Point (CurvatureDimension m T)) :
    ‖hessian (scaledCurvaturePopulation Θ A β) x-hessian (scaledCurvaturePopulation Θ A β) y‖≤
      (A*β^3*(curvatureGeometryConstant/((2*m:ℕ):ℝ)))*‖x-y‖ :=
  fderiv_gradient_lipschitz_of_third_bound (scaledCurvaturePopulation_contDiff Θ A β)
    (fun z => (scaledCurvaturePopulation_derivative_bounds Θ hm hA hβ z).2) y x

theorem scaledCurvaturePopulation_hessian_holder (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {A β ν : ℝ} (hA : 0≤A) (hβ : 0≤β) (hν : 0≤ν) (hν1 : ν≤1)
    (x y : Point (CurvatureDimension m T)) :
    ‖hessian (scaledCurvaturePopulation Θ A β) x-hessian (scaledCurvaturePopulation Θ A β) y‖≤
      (2*(A*β^2*(curvatureGeometryConstant/((2*m:ℕ):ℝ))))^(1-ν)*
      (A*β^3*(curvatureGeometryConstant/((2*m:ℕ):ℝ)))^ν*‖x-y‖^ν := by
  have hC := curvatureGeometryConstant_pos.le
  exact holder_of_bounded_lipschitz (hessian (scaledCurvaturePopulation Θ A β))
    (by positivity) (by positivity) hν hν1
    (fun z => (scaledCurvaturePopulation_derivative_bounds Θ hm hA hβ z).1)
    (scaledCurvaturePopulation_hessian_lipschitz Θ hm hA hβ) x y

end
end SecondOrder
