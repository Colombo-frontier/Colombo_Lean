import SecondOrder.PeriodicNoise
import SecondOrder.GateComposition

open scoped BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section
variable {m : ℕ}

def periodicEnergy (θ : BalancedVector m) (x : Point (2*m)) : ℝ := -periodicBlockPotential θ x

def periodicCompletion (θ : BalancedVector m) : Point (2*m) → ℝ := curvatureCompletion ∘ periodicEnergy θ

theorem periodicEnergy_eq (θ : BalancedVector m) (x : Point (2*m)) :
    periodicEnergy θ x = ‖periodicMean x θ‖^2/2 := by
  simp only [periodicEnergy, periodicBlockPotential, periodicPotential]
  ring

theorem periodicEnergy_mem (θ : BalancedVector m) (x : Point (2*m)) :
    periodicEnergy θ x ∈ Set.Icc (0:ℝ) (1/2) := by
  rw [periodicEnergy_eq]
  have hh := periodicMean_norm_le_one x θ
  constructor
  · positivity
  · nlinarith [norm_nonneg (periodicMean x θ)]

theorem periodicBlockPotential_nonpos (θ : BalancedVector m) (x : Point (2*m)) :
    periodicBlockPotential θ x ≤ 0 := by
  have hh := (periodicEnergy_mem θ x).1
  change 0 ≤ -periodicBlockPotential θ x at hh
  linarith

theorem periodicMean_zero (θ : BalancedVector m) : periodicMean (0 : Point (2*m)) θ = 0 := by
  simp only [periodicMean, balancedVectorSum, PiLp.zero_apply, Real.cos_zero, Real.sin_zero,
    one_mul, zero_mul, Finset.sum_const_zero, θ.property, zero_div]
  ext i
  fin_cases i <;> rfl

theorem periodicBlockPotential_zero (θ : BalancedVector m) : periodicBlockPotential θ 0 = 0 := by
  simp [periodicBlockPotential, periodicPotential, periodicMean_zero]

theorem periodicEnergy_zero (θ : BalancedVector m) : periodicEnergy θ 0 = 0 := by
  simp [periodicEnergy, periodicBlockPotential_zero]

theorem periodicEnergy_contDiff (θ : BalancedVector m) (k : WithTop ℕ∞) :
    ContDiff ℝ k (periodicEnergy θ) := (periodicBlockPotential_contDiff θ k).neg

theorem periodicEnergy_gradient (θ : BalancedVector m) :
    gradient (periodicEnergy θ) = fun x => -gradient (periodicBlockPotential θ) x := by
  funext x
  change (InnerProductSpace.toDual ℝ (Point (2*m))).symm
    (fderiv ℝ (fun y => -periodicBlockPotential θ y) x) = _
  rw [fderiv_neg, map_neg]
  rfl

theorem periodicEnergy_hessian (θ : BalancedVector m) (x : Point (2*m)) :
    hessian (periodicEnergy θ) x = -hessian (periodicBlockPotential θ) x := by
  rw [hessian, periodicEnergy_gradient, fderiv_neg]
  rfl

theorem periodicEnergy_gradient_sq_bound (θ : BalancedVector m) (x : Point (2*m)) :
    ‖gradient (periodicEnergy θ) x‖^2 ≤ ((2*m:ℕ):ℝ)⁻¹ := by
  simpa only [periodicEnergy_gradient, norm_neg] using periodicBlockPotential_gradient_sq_bound θ x

theorem periodicCompletion_contDiff (θ : BalancedVector m) : ContDiff ℝ 3 (periodicCompletion θ) :=
  curvatureCompletion_contDiff.comp (periodicEnergy_contDiff θ 3)

theorem periodicCompletion_mem (θ : BalancedVector m) (x : Point (2*m)) :
    periodicCompletion θ x ∈ Set.Icc (0:ℝ) 1 := gate_mem_Icc _

theorem periodicCompletion_flat (θ : BalancedVector m) (x : Point (2*m))
    (hx : ‖periodicMean x θ‖ ≤ 1/8) :
    periodicCompletion θ x = 0 ∧ gradient (periodicCompletion θ) x = 0 ∧
      hessian (periodicCompletion θ) x = 0 := by
  apply affineGate_composition_flat (periodicEnergy_contDiff θ 2) (by norm_num)
  rw [periodicEnergy_eq]
  nlinarith [norm_nonneg (periodicMean x θ)]

theorem periodicCompletion_zero (θ : BalancedVector m) : periodicCompletion θ 0 = 0 :=
  (periodicCompletion_flat θ 0 (by rw [periodicMean_zero]; norm_num)).1

theorem periodicCompletion_gt_half (θ : BalancedVector m) (x : Point (2*m))
    (hx : 1/4 < ‖periodicMean x θ‖) : 1/2 < periodicCompletion θ x := by
  apply curvatureCompletion_gt_half
  rw [periodicEnergy_eq]
  nlinarith

theorem periodicEnergy_unfinished (θ : BalancedVector m) (x : Point (2*m))
    (hx : ‖periodicMean x θ‖ ≤ 1/4) : periodicEnergy θ x ≤ 1/32 := by
  rw [periodicEnergy_eq]
  nlinarith [norm_nonneg (periodicMean x θ)]

theorem periodicCompletion_gradient (θ : BalancedVector m) (x : Point (2*m)) :
    gradient (periodicCompletion θ) x = deriv curvatureCompletion (periodicEnergy θ x) •
      gradient (periodicEnergy θ) x := by
  exact scalarComposition_gradient ((periodicEnergy_contDiff θ 1).differentiable (by norm_num) x)
    ((curvatureCompletion_contDiff.differentiable (by norm_num) _).hasDerivAt)

theorem periodicCompletion_hessian (θ : BalancedVector m) (x : Point (2*m)) :
    hessian (periodicCompletion θ) x =
      deriv curvatureCompletion (periodicEnergy θ x) • hessian (periodicEnergy θ) x+
      deriv (deriv curvatureCompletion) (periodicEnergy θ x) • rankOneMap (gradient (periodicEnergy θ) x) := by
  have he := affineGate_hessian (periodicEnergy_contDiff θ 2) (64/3) (1/128) x
  change hessian (periodicCompletion θ) x = _ at he
  rw [he]
  simp only [curvatureCompletion, deriv_affineGate, deriv_affineGateFirst]
  congr 1
  ext v
  simp only [rankOneMap, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    smul_smul, gradient, LinearIsometryEquiv.apply_symm_apply, smul_eq_mul]

theorem periodicCompletion_fisher (θ : BalancedVector m) (x : Point (2*m)) :
    ‖gradient (periodicCompletion θ) x‖^2 ≤
      (1225*(64/3:ℝ)^2/((2*m:ℕ):ℝ))*periodicCompletion θ x*(1-periodicCompletion θ x) := by
  have he := affineGate_gradient_fisher_bound
    ((periodicEnergy_contDiff θ 1).differentiable (by norm_num) x) (64/3) (1/128)
    (periodicEnergy_gradient_sq_bound θ x)
  convert he using 1 <;> ring

theorem periodicCompletion_hessian_bound (θ : BalancedVector m) (x : Point (2*m)) :
    ‖hessian (periodicCompletion θ) x‖ ≤ (140*(64/3:ℝ)*2+420*(64/3:ℝ)^2)/((2*m:ℕ):ℝ) := by
  have he := affineGate_hessian_bound (periodicEnergy_contDiff θ 2) (64/3) (1/128) x
  change ‖hessian (periodicCompletion θ) x‖ ≤ _ at he
  change ‖hessian (periodicCompletion θ) x‖ ≤ _
  have hH : ‖hessian (periodicEnergy θ) x‖ ≤ 2/((2*m:ℕ):ℝ) := by
    simpa only [periodicEnergy_hessian, norm_neg] using periodicBlockPotential_hessian_bound θ x
  have hg := periodicEnergy_gradient_sq_bound θ x
  have he' := add_le_add (mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ |(64/3:ℝ)| *140))
    (mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ (64/3:ℝ)^2*420))
  have hn : |(64/3:ℝ)| = (64/3:ℝ) := abs_of_nonneg (by norm_num)
  rw [hn] at he he'
  apply he.trans
  convert he' using 1 <;> ring

end
end SecondOrder
