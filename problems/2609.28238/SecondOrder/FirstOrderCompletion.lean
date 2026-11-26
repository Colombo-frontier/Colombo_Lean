import SecondOrder.FirstOrderBlockGeometry
import SecondOrder.GateComposition

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def firstOrderBlockCompletion (θ : Fin d → Bool) : Point d → ℝ :=
  firstOrderCompletion ∘ firstOrderBlockEncoding θ

theorem firstOrderBlockCompletion_contDiff (θ : Fin d → Bool) : ContDiff ℝ 3 (firstOrderBlockCompletion θ) :=
  firstOrderCompletion_contDiff.comp (firstOrderBlockEncoding_contDiff θ 3)

theorem firstOrderBlockCompletion_mem (θ : Fin d → Bool) (x : Point d) :
    0≤firstOrderBlockCompletion θ x ∧ firstOrderBlockCompletion θ x≤1 :=
  gate_mem_Icc _

@[simp] theorem firstOrderBlockCompletion_zero (θ : Fin d → Bool) : firstOrderBlockCompletion θ 0=0 := by
  change firstOrderCompletion (firstOrderCoefficientEncoding _ 0)=0
  rw [firstOrderCoefficientEncoding_zero]
  exact (firstOrderCompletion_flat (by norm_num : (0:ℝ)≤1/4)).1

theorem firstOrderBlockCompletion_gt_half (θ : Fin d → Bool) {x : Point d}
    (hx : 1/2<firstOrderBlockEncoding θ x) : 1/2<firstOrderBlockCompletion θ x :=
  firstOrderCompletion_gt_half hx

theorem firstOrderCompletion_deriv_nonneg (q : ℝ) : 0≤deriv firstOrderCompletion q := by
  rw [firstOrderCompletion,deriv_affineGate]
  exact mul_nonneg (by norm_num) (gateFirst_nonneg _)

theorem firstOrderBlockCompletion_gradient (θ : Fin d → Bool) (x : Point d) :
    gradient (firstOrderBlockCompletion θ) x=
      deriv firstOrderCompletion (firstOrderBlockEncoding θ x) • gradient (firstOrderBlockEncoding θ) x :=
  scalarComposition_gradient ((firstOrderBlockEncoding_contDiff θ 1).differentiable (by norm_num) x)
    ((firstOrderCompletion_contDiff.differentiable (by norm_num) _).hasDerivAt)

theorem firstOrderBlockCompletion_hessian (θ : Fin d → Bool) (x : Point d) :
    hessian (firstOrderBlockCompletion θ) x=
      deriv firstOrderCompletion (firstOrderBlockEncoding θ x) • hessian (firstOrderBlockEncoding θ) x+
      deriv (deriv firstOrderCompletion) (firstOrderBlockEncoding θ x) •
        rankOneMap (gradient (firstOrderBlockEncoding θ) x) := by
  have he := affineGate_hessian (firstOrderBlockEncoding_contDiff θ 2) 2 (1/4) x
  change hessian (firstOrderBlockCompletion θ) x=_ at he
  rw [he]
  simp only [firstOrderCompletion,deriv_affineGate,deriv_affineGateFirst]
  congr 1
  ext v
  simp only [rankOneMap,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,
    smul_smul,gradient,LinearIsometryEquiv.apply_symm_apply,smul_eq_mul]

theorem firstOrderBlockCompletion_flat (θ : Fin d → Bool) {x : Point d}
    (hx : firstOrderBlockEncoding θ x≤1/4) :
    firstOrderBlockCompletion θ x=0 ∧ gradient (firstOrderBlockCompletion θ) x=0 ∧
      hessian (firstOrderBlockCompletion θ) x=0 :=
  affineGate_composition_flat (firstOrderBlockEncoding_contDiff θ 2) (by norm_num) hx

theorem firstOrderBlockCompletion_fisher (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖gradient (firstOrderBlockCompletion θ) x‖^2≤
      19600*firstOrderBlockCompletion θ x*(1-firstOrderBlockCompletion θ x) := by
  have hg := firstOrderBlockEncoding_gradient_bound θ hd x
  have hgsq : ‖gradient (firstOrderBlockEncoding θ) x‖^2≤4 := by
    nlinarith [norm_nonneg (gradient (firstOrderBlockEncoding θ) x)]
  have hh := affineGate_gradient_fisher_bound
    ((firstOrderBlockEncoding_contDiff θ 1).differentiable (by norm_num) x) 2 (1/4) hgsq
  convert hh using 1 <;> norm_num [firstOrderBlockCompletion,firstOrderCompletion,Function.comp_def]

theorem firstOrderBlockCompletion_gradient_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖gradient (firstOrderBlockCompletion θ) x‖≤560 := by
  rw [firstOrderBlockCompletion_gradient,norm_smul]
  have hg := firstOrderBlockEncoding_gradient_bound θ hd x
  have hs : ‖deriv firstOrderCompletion (firstOrderBlockEncoding θ x)‖≤280 := by
    simpa only [firstOrderCompletion,deriv_affineGate] using
      (affineGateFirst_bound 2 (1/4) (firstOrderBlockEncoding θ x)).trans (by norm_num)
  exact (mul_le_mul hs hg (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem firstOrderBlockCompletion_hessian_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖hessian (firstOrderBlockCompletion θ) x‖≤7840 := by
  have hh := affineGate_hessian_bound (firstOrderBlockEncoding_contDiff θ 2) 2 (1/4) x
  change ‖hessian (firstOrderBlockCompletion θ) x‖≤_ at hh
  have hg := firstOrderBlockEncoding_gradient_bound θ hd x
  have hH := firstOrderBlockEncoding_hessian_bound θ hd x
  have hgsq : ‖gradient (firstOrderBlockEncoding θ) x‖^2≤4 := by
    nlinarith [norm_nonneg (gradient (firstOrderBlockEncoding θ) x)]
  norm_num at hh
  change ‖hessian (firstOrderBlockEncoding θ) x‖≤4 at hH
  change ‖hessian (firstOrderBlockCompletion θ) x‖≤
      280*‖hessian (firstOrderBlockEncoding θ) x‖+1680*‖gradient (firstOrderBlockEncoding θ) x‖^2 at hh
  linarith only [hh,hH,hgsq]

end
end SecondOrder
