import SecondOrder.FirstOrderCompletion

namespace SecondOrder
noncomputable section

theorem firstOrderCompletion_derivative_bounds (q : ℝ) :
    ‖deriv firstOrderCompletion q‖≤completionDerivativeBound ∧
    ‖deriv (deriv firstOrderCompletion) q‖≤completionDerivativeBound ∧
    ‖deriv (deriv (deriv firstOrderCompletion)) q‖≤completionDerivativeBound := by
  rw [firstOrderCompletion,deriv_affineGate,deriv_affineGateFirst,deriv_affineGateSecond]
  refine ⟨(affineGateFirst_bound 2 (1/4) q).trans (by norm_num [completionDerivativeBound]),
    (affineGateSecond_bound 2 (1/4) q).trans (by norm_num [completionDerivativeBound]),?_⟩
  have hh := (gate_derivative_bounds (2*(q-1/4))).2.2
  rw [deriv_gate,deriv_gateFirst,deriv_gateSecond] at hh
  have he : ‖affineGateThird 2 (1/4) q‖ = 8*‖gateThird (2*(q-1/4))‖ := by
    rw [affineGateThird,norm_mul]
    norm_num
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤8)
  exact hm.trans (by norm_num [completionDerivativeBound])

theorem firstOrderCompletion_first_lipschitz (q r : ℝ) :
    |deriv firstOrderCompletion r-deriv firstOrderCompletion q|≤completionDerivativeBound*|r-q| := by
  have hd (z : ℝ) : HasDerivAt (deriv firstOrderCompletion) (deriv (deriv firstOrderCompletion) z) z := by
    rw [firstOrderCompletion,deriv_affineGate,deriv_affineGateFirst]
    exact affineGateFirst_hasDerivAt _ _ _
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Set.univ) => (hd z).hasDerivWithinAt)
    (fun z _ => (firstOrderCompletion_derivative_bounds z).2.1)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ q) (Set.mem_univ r)

theorem firstOrderCompletion_second_lipschitz (q r : ℝ) :
    |deriv (deriv firstOrderCompletion) r-deriv (deriv firstOrderCompletion) q|≤completionDerivativeBound*|r-q| := by
  have hd (z : ℝ) : HasDerivAt (deriv (deriv firstOrderCompletion))
      (deriv (deriv (deriv firstOrderCompletion)) z) z := by
    rw [firstOrderCompletion,deriv_affineGate,deriv_affineGateFirst,deriv_affineGateSecond]
    exact affineGateSecond_hasDerivAt _ _ _
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Set.univ) => (hd z).hasDerivWithinAt)
    (fun z _ => (firstOrderCompletion_derivative_bounds z).2.2)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ q) (Set.mem_univ r)

private theorem smul_difference_estimate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : ℝ) (u v : E) : ‖s • u-t • v‖≤|s| * ‖u-v‖+|s-t| * ‖v‖ := by
  have he : s • u-t • v=s • (u-v)+(s-t) • v := by module
  rw [he]
  simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le (s • (u-v)) ((s-t) • v)

variable {d : ℕ}

theorem firstOrderBlockEncoding_rankOne_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖rankOneMap (gradient (firstOrderBlockEncoding θ) x)‖≤4 := by
  rw [rankOneMap,ContinuousLinearMap.norm_smulRight_apply,LinearIsometryEquiv.norm_map]
  have hh := firstOrderBlockEncoding_gradient_bound θ hd x
  nlinarith [norm_nonneg (gradient (firstOrderBlockEncoding θ) x)]

theorem firstOrderBlockEncoding_rankOne_lipschitz (θ : Fin d → Bool) (hd : 0<d) (x y : Point d) :
    ‖rankOneMap (gradient (firstOrderBlockEncoding θ) y)-rankOneMap (gradient (firstOrderBlockEncoding θ) x)‖≤16*‖y-x‖ := by
  apply (rankOneMap_sub_norm _ _).trans
  have hh := mul_le_mul
    (add_le_add (firstOrderBlockEncoding_gradient_bound θ hd y) (firstOrderBlockEncoding_gradient_bound θ hd x))
    (firstOrderBlockEncoding_gradient_lipschitz θ hd x y) (norm_nonneg _) (by norm_num : (0:ℝ)≤2+2)
  convert hh using 1 <;> ring

theorem firstOrderBlockCompletion_hessian_lipschitz (θ : Fin d → Bool) (hd : 0<d) (x y : Point d) :
    ‖hessian (firstOrderBlockCompletion θ) y-hessian (firstOrderBlockCompletion θ) x‖≤
      44*completionDerivativeBound*Real.sqrt d*‖y-x‖ := by
  let q := firstOrderBlockEncoding θ
  have hC : 0≤completionDerivativeBound := by norm_num [completionDerivativeBound]
  have h1 : |deriv firstOrderCompletion (q y)-deriv firstOrderCompletion (q x)|≤
      2*completionDerivativeBound*‖y-x‖ := by
    have hh := (firstOrderCompletion_first_lipschitz (q x) (q y)).trans
      (mul_le_mul_of_nonneg_left (firstOrderBlockEncoding_lipschitz θ hd x y) hC)
    convert hh using 1 <;> ring
  have h2 : |deriv (deriv firstOrderCompletion) (q y)-deriv (deriv firstOrderCompletion) (q x)|≤
      2*completionDerivativeBound*‖y-x‖ := by
    have hh := (firstOrderCompletion_second_lipschitz (q x) (q y)).trans
      (mul_le_mul_of_nonneg_left (firstOrderBlockEncoding_lipschitz θ hd x y) hC)
    convert hh using 1 <;> ring
  have hs1 : |deriv firstOrderCompletion (q y)|≤completionDerivativeBound := (firstOrderCompletion_derivative_bounds _).1
  have hs2 : |deriv (deriv firstOrderCompletion) (q y)|≤completionDerivativeBound := (firstOrderCompletion_derivative_bounds _).2.1
  have ht1 := smul_difference_estimate (deriv firstOrderCompletion (q y)) (deriv firstOrderCompletion (q x))
    (hessian q y) (hessian q x)
  have ht2 := smul_difference_estimate (deriv (deriv firstOrderCompletion) (q y)) (deriv (deriv firstOrderCompletion) (q x))
    (rankOneMap (gradient q y)) (rankOneMap (gradient q x))
  have hb1 := add_le_add
    (mul_le_mul hs1 (firstOrderBlockEncoding_hessian_lipschitz θ hd x y) (norm_nonneg _) hC)
    (mul_le_mul h1 (firstOrderBlockEncoding_hessian_bound θ hd x) (norm_nonneg _) (by positivity : 0≤2*completionDerivativeBound*‖y-x‖))
  have hb2 := add_le_add
    (mul_le_mul hs2 (firstOrderBlockEncoding_rankOne_lipschitz θ hd x y) (norm_nonneg _) hC)
    (mul_le_mul h2 (firstOrderBlockEncoding_rankOne_bound θ hd x) (norm_nonneg _) (by positivity : 0≤2*completionDerivativeBound*‖y-x‖))
  have he : hessian (firstOrderBlockCompletion θ) y-hessian (firstOrderBlockCompletion θ) x=
      (deriv firstOrderCompletion (q y) • hessian q y-deriv firstOrderCompletion (q x) • hessian q x)+
      (deriv (deriv firstOrderCompletion) (q y) • rankOneMap (gradient q y)-
        deriv (deriv firstOrderCompletion) (q x) • rankOneMap (gradient q x)) := by
    rw [firstOrderBlockCompletion_hessian,firstOrderBlockCompletion_hessian]
    dsimp [q]
    abel
  rw [he]
  apply (norm_add_le _ _).trans ((add_le_add (ht1.trans hb1) (ht2.trans hb2)).trans _)
  have hs : 1≤Real.sqrt (d:ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hd)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (norm_nonneg (y-x))
  nlinarith only [hh]

theorem firstOrderBlockCompletion_third_bound (θ : Fin d → Bool) (hd : 0<d) (x : Point d) :
    ‖iteratedFDeriv ℝ 3 (firstOrderBlockCompletion θ) x‖≤44*completionDerivativeBound*Real.sqrt d := by
  rw [norm_third_eq_norm_fderiv_hessian]
  apply norm_fderiv_le_of_lip' ℝ (by unfold completionDerivativeBound; positivity)
  exact Filter.Eventually.of_forall (fun y => firstOrderBlockCompletion_hessian_lipschitz θ hd x y)

end
end SecondOrder
