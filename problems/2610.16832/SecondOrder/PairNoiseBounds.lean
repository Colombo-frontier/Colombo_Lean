import SecondOrder.PairCosCalculus

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d : ℕ}

theorem cos_difference_bound (s t : ℝ) : |Real.cos t-Real.cos s| ≤ |t-s| := by
  simpa only [Real.norm_eq_abs, abs_neg, one_mul] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := (1:ℝ))
      (fun x (_ : x ∈ Set.univ) => (Real.hasDerivAt_cos x).hasDerivWithinAt)
      (fun x _ => by simpa only [Real.norm_eq_abs, abs_neg] using Real.abs_sin_le_one x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ s) (Set.mem_univ t)

theorem pairCosPotential_bound (a : UpperPair d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ e, |a e| ≤ A) (x : Point d) :
    |pairCosPotential a x| ≤ A*(d:ℝ)^2/2 := by
  calc
    _ ≤ ∑ e, |a e*Real.cos (x e.1.1-x e.1.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : UpperPair d, A := Finset.sum_le_sum (fun e _ => by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (ha e) (Real.abs_cos_le_one _) (abs_nonneg _) hA)
    _ = A*((d:ℝ)*((d:ℝ)-1)/2) := by simp [upperPair_card_real]; ring
    _ ≤ _ := by nlinarith [mul_nonneg hA (Nat.cast_nonneg (α := ℝ) d)]

theorem pairCosGradient_norm_bound (a : UpperPair d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ e, |a e| ≤ A) (x : Point d) : ‖pairCosGradient a x‖ ≤ A*(d:ℝ)*Real.sqrt d := by
  apply pairVectorSum_norm_bound _ hA
  intro e
  rw [abs_mul, abs_neg]
  simpa only [mul_one] using mul_le_mul (ha e) (Real.abs_sin_le_one _) (abs_nonneg _) hA

theorem pairCosHessian_norm_bound (a : UpperPair d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ e, |a e| ≤ A) (x : Point d) : ‖pairCosHessian a x‖ ≤ A*(d:ℝ) := by
  apply pairLaplacian_norm_bound _ hA
  intro e
  rw [abs_mul, abs_neg]
  simpa only [mul_one] using mul_le_mul (ha e) (Real.abs_cos_le_one _) (abs_nonneg _) hA

theorem pairCosHessian_lipschitz (a : UpperPair d → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ e, |a e| ≤ A) (x y : Point d) :
    ‖pairCosHessian a y-pairCosHessian a x‖ ≤ 2*A*(d:ℝ)*‖y-x‖ := by
  unfold pairCosHessian
  rw [pairLaplacian_sub]
  have he (e : UpperPair d) :
      |-a e*Real.cos (coordinateDifference e y)-(-a e*Real.cos (coordinateDifference e x))| ≤
        2*A*‖y-x‖ := by
    rw [← mul_sub, abs_mul, abs_neg]
    have hc : |Real.cos (coordinateDifference e y)-Real.cos (coordinateDifference e x)| ≤
        2*‖y-x‖ := by
      have hh := cos_difference_bound (coordinateDifference e x) (coordinateDifference e y)
      rw [← map_sub] at hh
      exact hh.trans (coordinateDifference_bound e (y-x))
    have hh := mul_le_mul (ha e) hc (abs_nonneg _) hA
    nlinarith [hh]
  have hh := pairLaplacian_norm_bound _ (by positivity : 0 ≤ 2*A*‖y-x‖) he
  convert hh using 1 <;> ring

theorem pairNoisePotential_value_bound (a : UpperPair d → ℝ) (hd : 0 < d)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ e, |a e| ≤ A) (x : Point d) :
    |pairNoisePotential a x| ≤ A/2 := by
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [pairNoisePotential, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((d:ℝ)⁻¹)^2*(A*(d:ℝ)^2/2) :=
      mul_le_mul_of_nonneg_left (pairCosPotential_bound a hA ha x) (sq_nonneg _)
    _ = _ := by field_simp

theorem pairNoisePotential_gradient_bound (a : UpperPair d → ℝ) (hd : 0 < d)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ e, |a e| ≤ A) (x : Point d) :
    ‖gradient (pairNoisePotential a) x‖ ≤ A/Real.sqrt d := by
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hS : Real.sqrt (d:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hd))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  rw [gradient_pairNoisePotential, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((d:ℝ)⁻¹)^2*(A*(d:ℝ)*Real.sqrt d) :=
      mul_le_mul_of_nonneg_left (pairCosGradient_norm_bound a hA ha x) (sq_nonneg _)
    _ = A*Real.sqrt d/(d:ℝ) := by field_simp <;> ring
    _ = _ := by
      apply (div_eq_div_iff hD hS).mpr
      calc
        _ = A*(Real.sqrt (d:ℝ))^2 := by ring
        _ = _ := by rw [hs]

theorem pairNoisePotential_hessian_bound (a : UpperPair d → ℝ) (hd : 0 < d)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ e, |a e| ≤ A) (x : Point d) :
    ‖hessian (pairNoisePotential a) x‖ ≤ A/(d:ℝ) := by
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [hessian_pairNoisePotential, norm_smul (-((d:ℝ)⁻¹)^2) (pairCosHessian a x), Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((d:ℝ)⁻¹)^2*(A*(d:ℝ)) :=
      mul_le_mul_of_nonneg_left (pairCosHessian_norm_bound a hA ha x) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

theorem pairNoisePotential_hessian_lipschitz (a : UpperPair d → ℝ) (hd : 0 < d)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ e, |a e| ≤ A) (x y : Point d) :
    ‖hessian (pairNoisePotential a) y-hessian (pairNoisePotential a) x‖ ≤ (2*A/(d:ℝ))*‖y-x‖ := by
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [hessian_pairNoisePotential, hessian_pairNoisePotential, ← smul_sub (-((d:ℝ)⁻¹)^2) (pairCosHessian a y) (pairCosHessian a x),
    norm_smul (-((d:ℝ)⁻¹)^2) (pairCosHessian a y-pairCosHessian a x), Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((d:ℝ)⁻¹)^2*(2*A*(d:ℝ)*‖y-x‖) :=
      mul_le_mul_of_nonneg_left (pairCosHessian_lipschitz a hA ha x y) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

theorem pairNoisePotential_third_bound (a : UpperPair d → ℝ) (hd : 0 < d)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ e, |a e| ≤ A) (x : Point d) :
    ‖iteratedFDeriv ℝ 3 (pairNoisePotential a) x‖ ≤ 2*A/(d:ℝ) := by
  rw [norm_third_eq_norm_fderiv_hessian]
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  exact Filter.Eventually.of_forall (fun y => pairNoisePotential_hessian_lipschitz a hd hA ha x y)

end
end SecondOrder
