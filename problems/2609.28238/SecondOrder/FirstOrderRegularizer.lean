import SecondOrder.FirstOrderBlockCalculus

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d : ℕ}

def firstOrderBlockRegularizer : Point d → ℝ :=
  separablePotential logCosh (fun _ => 8/(d:ℝ)) (Real.sqrt d)

theorem firstOrderBlockRegularizer_eq (x : Point d) :
    firstOrderBlockRegularizer x=(8/(d:ℝ))*∑ i, Real.log (Real.cosh (Real.sqrt d*x i)) := by
  unfold firstOrderBlockRegularizer separablePotential logCosh
  rw [Finset.mul_sum]

theorem firstOrderBlockRegularizer_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (firstOrderBlockRegularizer : Point d → ℝ) :=
  separablePotential_contDiff (logCosh_contDiff n) _ _

theorem firstOrderBlockRegularizer_nonneg (x : Point d) : 0≤firstOrderBlockRegularizer x := by
  unfold firstOrderBlockRegularizer separablePotential
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (logCosh_nonneg _))

@[simp] theorem firstOrderBlockRegularizer_zero : firstOrderBlockRegularizer (0:Point d)=0 := by
  simp [firstOrderBlockRegularizer,separablePotential]

theorem firstOrderBlockRegularizer_gradient :
    gradient (firstOrderBlockRegularizer : Point d → ℝ)=
      separableGradient Real.tanh (fun _ => 8/(d:ℝ)) (Real.sqrt d) :=
  gradient_separablePotential logCosh_hasDerivAt _ _

theorem firstOrderBlockRegularizer_gradient_apply (hd : 0<d) (x : Point d) (i : Fin d) :
    gradient firstOrderBlockRegularizer x i=(8/Real.sqrt d)*Real.tanh (Real.sqrt d*x i) := by
  rw [firstOrderBlockRegularizer_gradient]
  change (8/(d:ℝ))*Real.sqrt d*Real.tanh (Real.sqrt d*x i)=_
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hs : Real.sqrt (d:ℝ)≠0 := (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  field_simp [hD,hs]
  linear_combination (8*Real.tanh (Real.sqrt d*x i))*hsq

theorem firstOrderBlockRegularizer_hessian (x : Point d) :
    hessian firstOrderBlockRegularizer x=
      separableHessian tanhFirst (fun _ => 8/(d:ℝ)) (Real.sqrt d) x :=
  hessian_separablePotential logCosh_hasDerivAt tanh_hasDerivAt _ _ _

theorem firstOrderBlockRegularizer_gradient_bound (hd : 0<d) (x : Point d) :
    ‖gradient firstOrderBlockRegularizer x‖≤8 := by
  rw [firstOrderBlockRegularizer_gradient]
  have hh := separableGradient_norm_bound Real.tanh (fun _ : Fin d => 8/(d:ℝ))
    (Real.sqrt_nonneg (d:ℝ)) (show (0:ℝ)≤8/d by positivity) (by norm_num : (0:ℝ)≤1)
    (fun _ => le_of_eq (abs_of_nonneg (by positivity))) tanh_abs_le_one x
  apply hh.trans_eq
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  field_simp [hD]
  linear_combination 8*hs

theorem firstOrderBlockRegularizer_hessian_bound (hd : 0<d) (x : Point d) :
    ‖hessian firstOrderBlockRegularizer x‖≤8 := by
  rw [firstOrderBlockRegularizer_hessian]
  apply (separableHessian_norm_bound tanhFirst (fun _ : Fin d => 8/(d:ℝ))
    (show (0:ℝ)≤8/d by positivity) (by norm_num : (0:ℝ)≤1)
    (fun _ => le_of_eq (abs_of_nonneg (by positivity)))
    (fun t => by simpa only [abs_of_nonneg (tanhFirst_mem t).1] using (tanhFirst_mem t).2) x).trans_eq
  rw [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  field_simp [hD]

theorem firstOrderBlockRegularizer_hessian_lipschitz (hd : 0<d) (x y : Point d) :
    ‖hessian firstOrderBlockRegularizer y-hessian firstOrderBlockRegularizer x‖≤
      16*Real.sqrt d*‖y-x‖ := by
  rw [firstOrderBlockRegularizer_hessian,firstOrderBlockRegularizer_hessian]
  apply (separableHessian_lipschitz tanhFirst (fun _ : Fin d => 8/(d:ℝ))
    (Real.sqrt_nonneg (d:ℝ)) (show (0:ℝ)≤8/d by positivity) (by norm_num : (0:ℝ)≤2)
    (fun _ => le_of_eq (abs_of_nonneg (by positivity))) tanhFirst_difference x y).trans_eq
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  rw [pow_succ,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]
  field_simp [hD]
  <;> ring

theorem firstOrderBlockRegularizer_third_bound (hd : 0<d) (x : Point d) :
    ‖iteratedFDeriv ℝ 3 firstOrderBlockRegularizer x‖≤16*Real.sqrt d := by
  rw [norm_third_eq_norm_fderiv_hessian]
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  exact Filter.Eventually.of_forall (fun y => firstOrderBlockRegularizer_hessian_lipschitz hd x y)

end
end SecondOrder
