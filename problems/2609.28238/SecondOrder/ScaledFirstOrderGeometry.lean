import SecondOrder.ScaledFirstOrderLoss

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

theorem scaledFirstOrderPopulation_gap (Θ : Fin (T+1) → Fin d → Bool)
    {A : ℝ} (hA : 0≤A) (β : ℝ) (x : Point (FirstOrderDimension d T)) :
    scaledFirstOrderPopulation Θ A β 0-scaledFirstOrderPopulation Θ A β x≤20*A*(T+1:ℕ) := by
  simpa only [firstOrderScaledChain,scaledFirstOrderPopulation,scalarLinearScaling,map_zero] using
    firstOrderScaledChain_initial_gap Θ hA (firstOrderDilation d T β x)

theorem scaledFirstOrderPopulation_derivative_bounds (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (x : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderPopulation Θ A β) x‖≤A*β^2*firstOrderGeometryConstant ∧
    ‖iteratedFDeriv ℝ 3 (scaledFirstOrderPopulation Θ A β) x‖≤
      A*β^3*(firstOrderGeometryConstant*Real.sqrt d) := by
  let L := firstOrderDilation d T β
  have hL : ‖L‖≤β := by simpa only [abs_of_nonneg hβ] using firstOrderDilation_norm d T β
  have hM := firstOrderGeometryConstant_pos.le
  constructor
  · rw [hessian,norm_fderiv_gradient]
    exact scalarLinearScaling_iterated_bound_of_le _ hA hβ hM L hL 2
      ((firstOrderChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)) x
      (firstOrderChain_second_bound Θ hd (L x))
  · exact scalarLinearScaling_iterated_bound_of_le _ hA hβ (by positivity) L hL 3
      (firstOrderChain_contDiff Θ) x (firstOrderChain_third_bound Θ hd (L x))

theorem scaledFirstOrderPopulation_gradient_lipschitz (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (x y : Point (FirstOrderDimension d T)) :
    ‖gradient (scaledFirstOrderPopulation Θ A β) x-gradient (scaledFirstOrderPopulation Θ A β) y‖≤
      (A*β^2*firstOrderGeometryConstant)*‖x-y‖ := by
  apply gradient_lipschitz_of_second_bound
    ((scaledFirstOrderPopulation_contDiff Θ A β).of_le (show (2:WithTop ℕ∞)≤3 by decide)) _ y x
  intro z
  simpa only [hessian,norm_fderiv_gradient] using
    (scaledFirstOrderPopulation_derivative_bounds Θ hd hA hβ z).1

theorem scaledFirstOrderPopulation_hessian_lipschitz (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (x y : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderPopulation Θ A β) x-hessian (scaledFirstOrderPopulation Θ A β) y‖≤
      (A*β^3*(firstOrderGeometryConstant*Real.sqrt d))*‖x-y‖ :=
  fderiv_gradient_lipschitz_of_third_bound (scaledFirstOrderPopulation_contDiff Θ A β)
    (fun z => (scaledFirstOrderPopulation_derivative_bounds Θ hd hA hβ z).2) y x

theorem scaledFirstOrderPopulation_hessian_holder (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {A β ν : ℝ} (hA : 0≤A) (hβ : 0≤β) (hν : 0≤ν) (hν1 : ν≤1)
    (x y : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderPopulation Θ A β) x-hessian (scaledFirstOrderPopulation Θ A β) y‖≤
      (2*(A*β^2*firstOrderGeometryConstant))^(1-ν)*
      (A*β^3*(firstOrderGeometryConstant*Real.sqrt d))^ν*‖x-y‖^ν := by
  have hC := firstOrderGeometryConstant_pos.le
  exact holder_of_bounded_lipschitz (hessian (scaledFirstOrderPopulation Θ A β))
    (by positivity) (by positivity) hν hν1
    (fun z => (scaledFirstOrderPopulation_derivative_bounds Θ hd hA hβ z).1)
    (scaledFirstOrderPopulation_hessian_lipschitz Θ hd hA hβ) x y

end
end SecondOrder
