import SecondOrder.FirstOrderSeparation

namespace SecondOrder
noncomputable section
variable {d : ℕ}

theorem firstOrderBlockEncoding_abs_le (θ : Fin d → Bool) (x : Point d) :
    |firstOrderBlockEncoding θ x|≤2 := by
  rw [firstOrderBlockEncoding_eq]
  exact firstOrderEncoding_abs_le _ _

theorem firstOrderBlockEncoding_gradient_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖gradient (firstOrderBlockEncoding θ) x‖≤2 := by
  simpa only [mul_one] using firstOrderCoefficientEncoding_gradient_bound (fun i => signValue (θ i)) hd
    (by norm_num : (0:ℝ)≤1) (fun i => by cases hi : θ i <;> norm_num [hi,signValue]) x

theorem firstOrderBlockEncoding_hessian_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖hessian (firstOrderBlockEncoding θ) x‖≤4 := by
  simpa only [mul_one] using firstOrderCoefficientEncoding_hessian_bound (fun i => signValue (θ i)) hd
    (by norm_num : (0:ℝ)≤1) (fun i => by cases hi : θ i <;> norm_num [hi,signValue]) x

theorem firstOrderBlockEncoding_third_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖iteratedFDeriv ℝ 3 (firstOrderBlockEncoding θ) x‖≤12*Real.sqrt d := by
  simpa only [mul_one] using firstOrderCoefficientEncoding_third_bound (fun i => signValue (θ i)) hd
    (by norm_num : (0:ℝ)≤1) (fun i => by cases hi : θ i <;> norm_num [hi,signValue]) x

theorem firstOrderBlockEncoding_lipschitz (θ : Fin d → Bool) (hd : 0<d) (x y : Point d) :
    |firstOrderBlockEncoding θ y-firstOrderBlockEncoding θ x|≤2*‖y-x‖ := by
  have hf (z : Point d) : ‖fderiv ℝ (firstOrderBlockEncoding θ) z‖≤2 := by
    simpa only [gradient,LinearIsometryEquiv.norm_map] using firstOrderBlockEncoding_gradient_bound θ hd z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => (firstOrderBlockEncoding_contDiff θ 1).differentiable (by norm_num) z)
    (fun z _ => hf z) (convex_univ : Convex ℝ (Set.univ : Set (Point d)))
    (Set.mem_univ x) (Set.mem_univ y)

theorem firstOrderBlockEncoding_gradient_lipschitz (θ : Fin d → Bool) (hd : 0<d) (x y : Point d) :
    ‖gradient (firstOrderBlockEncoding θ) y-gradient (firstOrderBlockEncoding θ) x‖≤4*‖y-x‖ := by
  apply gradient_lipschitz_of_second_bound (firstOrderBlockEncoding_contDiff θ 2)
  intro z
  rw [←norm_fderiv_gradient]
  exact firstOrderBlockEncoding_hessian_bound θ hd z

theorem firstOrderBlockEncoding_hessian_lipschitz (θ : Fin d → Bool) (hd : 0<d) (x y : Point d) :
    ‖hessian (firstOrderBlockEncoding θ) y-hessian (firstOrderBlockEncoding θ) x‖≤12*Real.sqrt d*‖y-x‖ := by
  simpa only [mul_one] using firstOrderCoefficientEncoding_hessian_lipschitz (fun i => signValue (θ i)) hd
    (by norm_num : (0:ℝ)≤1) (fun i => by cases hi : θ i <;> norm_num [hi,signValue]) x y

def firstOrderBlockEnergy (θ : Fin d → Bool) (B : ℝ) (x : Point d) : ℝ :=
  B*firstOrderBlockEncoding θ x+firstOrderBlockRegularizer x

theorem firstOrderBlockEnergy_gradient (θ : Fin d → Bool) (B : ℝ) (hd : 0<d) (x : Point d) :
    gradient (firstOrderBlockEnergy θ B) x=(1/Real.sqrt d) • firstOrderBlockForce θ B x := by
  have hq := (firstOrderBlockEncoding_contDiff θ 1).differentiable (by norm_num)
  have hr := (firstOrderBlockRegularizer_contDiff (d := d) 1).differentiable (by norm_num)
  unfold firstOrderBlockEnergy
  rw [gradient_add_scalar ((differentiable_const B).mul hq) hr,gradient_const_mul_scalar hq]
  ext i
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,firstOrderBlockForce,euclideanVector_apply]
  change B*gradient (firstOrderCoefficientEncoding (fun j => signValue (θ j))) x i+
    gradient firstOrderBlockRegularizer x i=_
  rw [firstOrderCoefficientEncoding_gradient_apply _ hd,firstOrderBlockRegularizer_gradient_apply hd]
  ring

/-- An unfinished block cannot have small gradient when the incoming and
outgoing chain coefficients sum to B≤−2. -/
theorem firstOrderBlockEnergy_gradient_lower (θ : Fin d → Bool) {B : ℝ} (hB : B≤-2) (hd : 0<d)
    (x : Point d) (hx : firstOrderBlockEncoding θ x≤1/2) :
    firstOrderGradientConstant≤‖gradient (firstOrderBlockEnergy θ B) x‖ := by
  rw [firstOrderBlockEnergy_gradient θ B hd,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ)≤1/Real.sqrt d by positivity)]
  have hs : 0<Real.sqrt (d:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  have hh := firstOrderBlockForce_lower θ hB hd x hx
  have hh' : Real.sqrt d*(firstOrderGradientConstant*Real.sqrt d)≤Real.sqrt d*‖firstOrderBlockForce θ B x‖ := by
    convert hh using 1
    linear_combination firstOrderGradientConstant*hsq
  have hl := (mul_le_mul_left hs).1 hh'
  have hv := (le_div_iff₀ hs).2 hl
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using hv

end
end SecondOrder
