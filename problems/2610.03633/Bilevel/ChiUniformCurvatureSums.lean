import Bilevel.ChiCurvatureFloors

/-! Sharp Hessian-scale powers for the actual nonuniform source schedule.
The ratio bound is T^(3/4), rather than T; this distinction is essential
for the full accuracy window when theta reaches kappa squared. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCurvatureSchedule

theorem ratio_rpow_formula {T : ℝ} (hT : 0<T) (j : ℕ) :
    curvature T (j+1)/curvature T j = T^(3/(4:ℝ)^(j+1)) := by
  unfold curvature
  rw [← Real.rpow_sub hT]
  congr 1
  rw [pow_succ]
  field_simp
  ring

theorem ratio_le_three_quarters {T : ℝ} (hT : 1≤T) (j : ℕ) :
    curvature T (j+1)/curvature T j≤T^(3/4:ℝ) := by
  rw [ratio_rpow_formula (by linarith : 0<T)]
  apply Real.rpow_le_rpow_of_exponent_le hT
  have hp : (1:ℝ)≤4^j := one_le_pow₀ (by norm_num)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4^(j+1))).mpr
  rw [pow_succ]
  linarith

theorem ratio_sqrt_le {T : ℝ} (hT : 1≤T) (j : ℕ) :
    Real.sqrt (curvature T (j+1)/curvature T j)≤T^(3/8:ℝ) := by
  have hr : 0≤curvature T (j+1)/curvature T j :=
    (curvature_ratio_ge_one hT j).trans' zero_le_one
  rw [Real.sqrt_eq_rpow]
  have hh := Real.rpow_le_rpow hr (ratio_le_three_quarters hT j) (by norm_num : (0:ℝ)≤1/2)
  rw [← Real.rpow_mul (by linarith : 0≤T)] at hh
  norm_num at hh
  exact hh

theorem length_cube_le_quarter {cn η T : ℝ} (hcn : 0≤cn) (hT : 1≤T) (j : ℕ) :
    (length cn η T j:ℝ)^(1/3:ℝ)≤(cn/η^2)^(1/3:ℝ)*T^(1/4:ℝ) := by
  have hTp : 0<T := by linarith
  have hr := div_pos (curvature_pos hTp (j+1)) (curvature_pos hTp j)
  have hf := Real.rpow_le_rpow (show (0:ℝ)≤(length cn η T j:ℝ) by positivity)
    (length_upper hcn hTp j) (by norm_num : (0:ℝ)≤1/3)
  rw [show cn*(curvature T (j+1)/curvature T j)/η^2=
    (cn/η^2)*(curvature T (j+1)/curvature T j) by ring,
    Real.mul_rpow (div_nonneg hcn (sq_nonneg η)) hr.le] at hf
  have hg := Real.rpow_le_rpow hr.le (ratio_le_three_quarters hT j) (by norm_num : (0:ℝ)≤1/3)
  rw [← Real.rpow_mul hTp.le] at hg
  norm_num at hg
  exact hf.trans (mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (by positivity) _))

theorem length_two_thirds_le_sqrt {cn η T : ℝ} (hcn : 0≤cn) (hT : 1≤T) (j : ℕ) :
    ((length cn η T j:ℝ)^(1/3:ℝ))^2≤(cn/η^2)^(2/3:ℝ)*Real.sqrt T := by
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
    (length_cube_le_quarter (η:=η) hcn hT j) 2
  rw [mul_pow,← Real.rpow_natCast ((cn/η^2)^(1/3:ℝ)) 2,
    ← Real.rpow_mul (div_nonneg hcn (sq_nonneg η)),
    ← Real.rpow_natCast (T^(1/4:ℝ)) 2,← Real.rpow_mul (by linarith : 0≤T)] at hh
  norm_num at hh
  simpa only [Real.sqrt_eq_rpow] using hh

theorem weighted_length_hessian_sum {cn η T : ℝ} (hcn : 0≤cn) (hη : 0≤η)
    (hη1 : η≤1) (hT : 1≤T) (J : ℕ) :
    (∑ i : Fin J,η^(i.val+1)*((length cn η T i.val:ℝ)^(1/3:ℝ))^2)≤
      (J:ℝ)*(cn/η^2)^(2/3:ℝ)*Real.sqrt T := by
  have hi (i : Fin J) : η^(i.val+1)*((length cn η T i.val:ℝ)^(1/3:ℝ))^2≤
      (cn/η^2)^(2/3:ℝ)*Real.sqrt T := by
    calc
      _≤1*((cn/η^2)^(2/3:ℝ)*Real.sqrt T) := mul_le_mul
        (pow_le_one₀ hη hη1) (length_two_thirds_le_sqrt hcn hT i.val)
        (sq_nonneg _) zero_le_one
      _=_ := one_mul _
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh

theorem weighted_radial_hessian_sum {η T : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (hT : 1≤T) (J : ℕ) :
    (∑ i : Fin J,η^i.val*Real.sqrt (curvature T (i.val+1)/curvature T i.val))≤
      (J:ℝ)*T^(3/8:ℝ) := by
  have hi (i : Fin J) : η^i.val*Real.sqrt (curvature T (i.val+1)/curvature T i.val)≤
      T^(3/8:ℝ) := by
    simpa only [one_mul] using mul_le_mul (pow_le_one₀ hη hη1) (ratio_sqrt_le hT i.val)
      (Real.sqrt_nonneg _) zero_le_one
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

end Bilevel.ChiCurvatureSchedule
