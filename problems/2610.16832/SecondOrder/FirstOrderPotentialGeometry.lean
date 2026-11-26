import SecondOrder.FirstOrderNoise
import SecondOrder.FirstOrderChainGradient

namespace SecondOrder
noncomputable section
variable {d : ℕ}

theorem firstOrderBlockPotential_gradient (θ : Fin d → Bool) :
    gradient (firstOrderBlockPotential θ)=fun x => (-2:ℝ) • gradient (firstOrderBlockEncoding θ) x := by
  funext x
  have he : fderiv ℝ (firstOrderBlockPotential θ) x=(-2:ℝ) • fderiv ℝ (firstOrderBlockEncoding θ) x := by
    ext v
    exact firstOrderBlockPotential_fderiv θ x v
  simp only [gradient,he,map_smul]

theorem firstOrderBlockPotential_hessian (θ : Fin d → Bool) (x : Point d) :
    hessian (firstOrderBlockPotential θ) x=(-2:ℝ) • hessian (firstOrderBlockEncoding θ) x := by
  rw [hessian,firstOrderBlockPotential_gradient]
  exact fderiv_const_smul
    ((contDiff_gradient_one (firstOrderBlockEncoding_contDiff θ 2)).differentiable (by norm_num) x) (-2)

theorem firstOrderBlockPotential_gradient_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖gradient (firstOrderBlockPotential θ) x‖≤4 := by
  rw [firstOrderBlockPotential_gradient,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith [firstOrderBlockEncoding_gradient_bound θ hd x]

theorem firstOrderBlockPotential_hessian_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖hessian (firstOrderBlockPotential θ) x‖≤8 := by
  rw [firstOrderBlockPotential_hessian,norm_smul (-2:ℝ) (hessian (firstOrderBlockEncoding θ) x)]
  norm_num only [Real.norm_eq_abs,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith [firstOrderBlockEncoding_hessian_bound θ hd x]

theorem firstOrderBlockPotential_hessian_lipschitz (θ : Fin d → Bool) (hd : 0<d) (x y : Point d) :
    ‖hessian (firstOrderBlockPotential θ) y-hessian (firstOrderBlockPotential θ) x‖≤24*Real.sqrt d*‖y-x‖ := by
  rw [firstOrderBlockPotential_hessian,firstOrderBlockPotential_hessian,
    ←smul_sub (-2:ℝ) (hessian (firstOrderBlockEncoding θ) y) (hessian (firstOrderBlockEncoding θ) x),
    norm_smul (-2:ℝ) (hessian (firstOrderBlockEncoding θ) y-hessian (firstOrderBlockEncoding θ) x)]
  norm_num only [Real.norm_eq_abs,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith [firstOrderBlockEncoding_hessian_lipschitz θ hd x y]

theorem firstOrderBlockPotential_third_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖iteratedFDeriv ℝ 3 (firstOrderBlockPotential θ) x‖≤24*Real.sqrt d := by
  rw [norm_third_eq_norm_fderiv_hessian]
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  exact Filter.Eventually.of_forall (fun y => firstOrderBlockPotential_hessian_lipschitz θ hd x y)

theorem firstOrderBlock_sample_C21 (θ : Fin d → Bool) (hd : 0<d) (R : ℝ) (hR : 2≤R)
    (z : Fin d → SignedCoefficient R) :
    ContDiff ℝ 2 (sampledFirstOrderPotential z) ∧ ∃ C : ℝ, 0≤C ∧
      ∀ x y, ‖hessian (sampledFirstOrderPotential z) y-hessian (sampledFirstOrderPotential z) x‖≤C*‖y-x‖ := by
  refine ⟨sampledFirstOrderPotential_contDiff z 2,(24*(R+1)+24)*Real.sqrt d,by positivity,?_⟩
  intro x y
  have he : hessian (sampledFirstOrderPotential z) y-hessian (sampledFirstOrderPotential z) x=
      (hessian (firstOrderBlockNoise θ z) y-hessian (firstOrderBlockNoise θ z) x)+
      (hessian (firstOrderBlockPotential θ) y-hessian (firstOrderBlockPotential θ) x) := by
    rw [firstOrderBlockNoise_hessian,firstOrderBlockNoise_hessian]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hh := add_le_add (firstOrderBlockNoise_hessian_lipschitz θ hd R hR z x y)
    (firstOrderBlockPotential_hessian_lipschitz θ hd x y)
  convert hh using 1 <;> ring

end
end SecondOrder
