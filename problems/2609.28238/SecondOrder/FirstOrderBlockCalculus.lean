import SecondOrder.SeparableCalculus

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d : ℕ}

/-- The actual finite-feature correlation, allowing arbitrary coefficients
so the same derivative proof also covers sampled and centered fields. -/
def firstOrderCoefficientEncoding (a : Fin d → ℝ) : Point d → ℝ :=
  separablePotential Real.tanh (fun i => (2/(d:ℝ))*a i) (Real.sqrt d)

def firstOrderBlockEncoding (θ : Fin d → Bool) : Point d → ℝ :=
  firstOrderCoefficientEncoding (fun i => signValue (θ i))

theorem firstOrderBlockEncoding_eq (θ : Fin d → Bool) (x : Point d) :
    firstOrderBlockEncoding θ x=firstOrderEncoding (fun i => x i) θ := by
  unfold firstOrderBlockEncoding firstOrderCoefficientEncoding separablePotential firstOrderEncoding rademacherSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem firstOrderCoefficientEncoding_contDiff (a : Fin d → ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (firstOrderCoefficientEncoding a) :=
  separablePotential_contDiff (tanh_contDiff n) _ _

theorem firstOrderBlockEncoding_contDiff (θ : Fin d → Bool) (n : WithTop ℕ∞) :
    ContDiff ℝ n (firstOrderBlockEncoding θ) := firstOrderCoefficientEncoding_contDiff _ n

@[simp] theorem firstOrderCoefficientEncoding_zero (a : Fin d → ℝ) : firstOrderCoefficientEncoding a 0=0 := by
  simp [firstOrderCoefficientEncoding,separablePotential,Real.tanh_zero]

theorem firstOrderCoefficientEncoding_gradient (a : Fin d → ℝ) :
    gradient (firstOrderCoefficientEncoding a)=
      separableGradient tanhFirst (fun i => (2/(d:ℝ))*a i) (Real.sqrt d) :=
  gradient_separablePotential tanh_hasDerivAt _ _

theorem firstOrderCoefficientEncoding_gradient_apply (a : Fin d → ℝ) (hd : 0<d)
    (x : Point d) (i : Fin d) :
    gradient (firstOrderCoefficientEncoding a) x i=(2/Real.sqrt d)*a i*tanhFirst (Real.sqrt d*x i) := by
  rw [firstOrderCoefficientEncoding_gradient]
  change (2/(d:ℝ))*a i*Real.sqrt d*tanhFirst (Real.sqrt d*x i)=_
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hs : Real.sqrt (d:ℝ)≠0 := (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  field_simp [hD,hs]
  linear_combination (2*a i*tanhFirst (Real.sqrt d*x i))*hsq

theorem firstOrderCoefficientEncoding_hessian (a : Fin d → ℝ) (x : Point d) :
    hessian (firstOrderCoefficientEncoding a) x=
      separableHessian tanhSecond (fun i => (2/(d:ℝ))*a i) (Real.sqrt d) x :=
  hessian_separablePotential tanh_hasDerivAt tanhFirst_hasDerivAt _ _ _

theorem firstOrderCoefficientEncoding_value_bound (a : Fin d → ℝ) (hd : 0<d)
    {W : ℝ} (hW : 0≤W) (ha : ∀ i, |a i|≤W) (x : Point d) :
    |firstOrderCoefficientEncoding a x|≤2*W := by
  have hD : (0:ℝ)<d := by exact_mod_cast hd
  unfold firstOrderCoefficientEncoding separablePotential
  calc
    _ ≤ ∑ i, |(2/(d:ℝ))*a i*Real.tanh (Real.sqrt d*x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (2/(d:ℝ))*W := by
      apply Finset.sum_le_sum
      intro i _
      simp only [abs_mul,abs_of_nonneg (show (0:ℝ)≤2/d by positivity)]
      simpa only [mul_one] using mul_le_mul
        (mul_le_mul_of_nonneg_left (ha i) (by positivity : (0:ℝ)≤2/d))
        (tanh_abs_le_one _) (abs_nonneg _) (by positivity : 0≤(2/(d:ℝ))*W)
    _ = _ := by simp; field_simp

theorem firstOrderCoefficientEncoding_coefficient_bound (a : Fin d → ℝ)
    {W : ℝ} (ha : ∀ i, |a i|≤W) (i : Fin d) : |(2/(d:ℝ))*a i|≤(2/(d:ℝ))*W := by
  rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤2/d by positivity)]
  exact mul_le_mul_of_nonneg_left (ha i) (by positivity)

theorem firstOrderCoefficientEncoding_gradient_bound (a : Fin d → ℝ) (hd : 0<d)
    {W : ℝ} (hW : 0≤W) (ha : ∀ i, |a i|≤W) (x : Point d) :
    ‖gradient (firstOrderCoefficientEncoding a) x‖≤2*W := by
  rw [firstOrderCoefficientEncoding_gradient]
  have hh := separableGradient_norm_bound tanhFirst (fun i => (2/(d:ℝ))*a i)
    (Real.sqrt_nonneg (d:ℝ)) (show 0≤(2/(d:ℝ))*W by positivity) (by norm_num : (0:ℝ)≤1)
    (firstOrderCoefficientEncoding_coefficient_bound a ha)
    (fun t => by simpa only [abs_of_nonneg (tanhFirst_mem t).1] using (tanhFirst_mem t).2) x
  apply hh.trans_eq
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  field_simp [hD]
  linear_combination (2*W)*hs

theorem firstOrderCoefficientEncoding_hessian_bound (a : Fin d → ℝ) (hd : 0<d)
    {W : ℝ} (hW : 0≤W) (ha : ∀ i, |a i|≤W) (x : Point d) :
    ‖hessian (firstOrderCoefficientEncoding a) x‖≤4*W := by
  rw [firstOrderCoefficientEncoding_hessian]
  apply (separableHessian_norm_bound tanhSecond (fun i => (2/(d:ℝ))*a i)
    (show 0≤(2/(d:ℝ))*W by positivity) (by norm_num : (0:ℝ)≤2)
    (firstOrderCoefficientEncoding_coefficient_bound a ha) tanhSecond_abs_le x).trans_eq
  rw [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  field_simp [hD]
  <;> ring

theorem firstOrderCoefficientEncoding_hessian_lipschitz (a : Fin d → ℝ) (hd : 0<d)
    {W : ℝ} (hW : 0≤W) (ha : ∀ i, |a i|≤W) (x y : Point d) :
    ‖hessian (firstOrderCoefficientEncoding a) y-hessian (firstOrderCoefficientEncoding a) x‖≤
      12*W*Real.sqrt d*‖y-x‖ := by
  rw [firstOrderCoefficientEncoding_hessian,firstOrderCoefficientEncoding_hessian]
  apply (separableHessian_lipschitz tanhSecond (fun i => (2/(d:ℝ))*a i)
    (Real.sqrt_nonneg (d:ℝ)) (show 0≤(2/(d:ℝ))*W by positivity) (by norm_num : (0:ℝ)≤6)
    (firstOrderCoefficientEncoding_coefficient_bound a ha) tanhSecond_difference x y).trans_eq
  have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  rw [pow_succ,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]
  field_simp [hD]
  <;> ring

theorem firstOrderCoefficientEncoding_third_bound (a : Fin d → ℝ) (hd : 0<d)
    {W : ℝ} (hW : 0≤W) (ha : ∀ i, |a i|≤W) (x : Point d) :
    ‖iteratedFDeriv ℝ 3 (firstOrderCoefficientEncoding a) x‖≤12*W*Real.sqrt d := by
  rw [norm_third_eq_norm_fderiv_hessian]
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  exact Filter.Eventually.of_forall (fun y => firstOrderCoefficientEncoding_hessian_lipschitz a hd hW ha x y)

end
end SecondOrder
