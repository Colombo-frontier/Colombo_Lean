import SecondOrder.FirstOrderCompletion

/-! Weighted second derivatives of the manuscript's concrete septic gate. -/

open SecondOrder
namespace SampleReuse
noncomputable section

theorem gate_second_fisher_polynomial {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gateD2 t ^ 2 ≤ 176400 * gatePoly t * (1 - gatePoly t) := by
  have hprod : t ^ 4 * (1 - t) ^ 4 ≤ gatePoly t * (1 - gatePoly t) :=
    mul_le_mul (gatePoly_lower ht0 ht1) (gatePoly_complement_lower ht0 ht1)
      (by positivity) (gatePoly_mem_Icc ht0 ht1).1
  have hs : (1 - 2 * t) ^ 2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  calc
    gateD2 t ^ 2 = 176400 * (t ^ 4 * (1 - t) ^ 4) * (1 - 2 * t) ^ 2 := by
      unfold gateD2
      ring
    _ ≤ 176400 * (t ^ 4 * (1 - t) ^ 4) * 1 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ _ := by simpa only [mul_one, mul_assoc] using
      mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 176400)

theorem gate_second_fisher (x : ℝ) :
    (deriv (deriv gate) x) ^ 2 ≤ 176400 * gate x * (1 - gate x) := by
  rw [deriv_gate, deriv_gateFirst, gate_eq_unitClipped]
  change (unitClipped gateD2 x) ^ 2 ≤
    176400 * unitClipped gatePoly x * (1 - unitClipped gatePoly x)
  simp only [unitClipped_eq_comp, Function.comp_apply]
  exact gate_second_fisher_polynomial (unitClip_mem x).1 (unitClip_mem x).2

theorem firstOrderCompletion_second_fisher (x : ℝ) :
    (deriv (deriv firstOrderCompletion) x) ^ 2 ≤
      2822400 * firstOrderCompletion x * (1 - firstOrderCompletion x) := by
  have hh := gate_second_fisher (2 * (x - 1 / 4))
  simp only [firstOrderCompletion, deriv_affineGate, deriv_affineGateFirst,
    affineGateSecond, affineGate, deriv_gate, deriv_gateFirst] at hh ⊢
  nlinarith

theorem firstOrderCompletion_first_fisher (x : ℝ) :
    (deriv firstOrderCompletion x) ^ 2 ≤
      4900 * firstOrderCompletion x * (1 - firstOrderCompletion x) := by
  have hh := affineGate_fisher 2 (1 / 4) x
  simpa only [firstOrderCompletion, show (1225 : ℝ) * 2 ^ 2 = 4900 by norm_num] using hh

theorem firstOrderBlockCompletion_second_fisher {d : ℕ} (θ : Fin d → Bool)
    (hd : 0 < d) (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (firstOrderBlockCompletion θ)) x‖ ^ 2 ≤
      (10000 : ℝ) ^ 2 * firstOrderBlockCompletion θ x * (1 - firstOrderBlockCompletion θ x) := by
  rw [← norm_hessian_eq_second_fderiv]
  change ‖hessian (firstOrderBlockCompletion θ) x‖ ^ 2 ≤ _
  let q := firstOrderBlockEncoding θ x
  have h1 := firstOrderCompletion_first_fisher q
  have h2 := firstOrderCompletion_second_fisher q
  have hval := firstOrderBlockCompletion_mem θ x
  have hg := firstOrderBlockEncoding_gradient_bound θ hd x
  have hH := firstOrderBlockEncoding_hessian_bound θ hd x
  have hgsq : ‖gradient (firstOrderBlockEncoding θ) x‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (gradient (firstOrderBlockEncoding θ) x)]
  have hn : ‖hessian (firstOrderBlockCompletion θ) x‖ ≤
      4 * |deriv firstOrderCompletion q| + 4 * |deriv (deriv firstOrderCompletion) q| := by
    rw [firstOrderBlockCompletion_hessian]
    apply (norm_add_le _ _).trans
    rw [norm_smul (deriv firstOrderCompletion q) (hessian (firstOrderBlockEncoding θ) x),
      norm_smul (deriv (deriv firstOrderCompletion) q)
        (rankOneMap (gradient (firstOrderBlockEncoding θ) x)), Real.norm_eq_abs, Real.norm_eq_abs]
    have hr : ‖rankOneMap (gradient (firstOrderBlockEncoding θ) x)‖ =
        ‖gradient (firstOrderBlockEncoding θ) x‖ ^ 2 := by
      simp only [rankOneMap, ContinuousLinearMap.norm_smulRight_apply, LinearIsometryEquiv.norm_map,
        pow_two]
    rw [hr]
    have hH' : ‖hessian (firstOrderBlockEncoding θ) x‖ ≤ 4 := hH
    have ha := mul_le_mul_of_nonneg_left hH' (abs_nonneg (deriv firstOrderCompletion q))
    have hb := mul_le_mul_of_nonneg_left hgsq (abs_nonneg (deriv (deriv firstOrderCompletion) q))
    dsimp only [q] at ha hb
    nlinarith only [ha, hb]
  have hn0 := norm_nonneg (hessian (firstOrderBlockCompletion θ) x)
  have habs1 := abs_nonneg (deriv firstOrderCompletion q)
  have habs2 := abs_nonneg (deriv (deriv firstOrderCompletion) q)
  have hnsq : ‖hessian (firstOrderBlockCompletion θ) x‖ ^ 2 ≤
      32 * (deriv firstOrderCompletion q) ^ 2 + 32 * (deriv (deriv firstOrderCompletion) q) ^ 2 := by
    nlinarith [sq_abs (deriv firstOrderCompletion q), sq_abs (deriv (deriv firstOrderCompletion) q),
      sq_nonneg (|deriv firstOrderCompletion q| - |deriv (deriv firstOrderCompletion) q|)]
  have hv : 0 ≤ firstOrderBlockCompletion θ x * (1 - firstOrderBlockCompletion θ x) :=
    mul_nonneg hval.1 (sub_nonneg.mpr hval.2)
  change (deriv firstOrderCompletion q) ^ 2 ≤
    4900 * firstOrderBlockCompletion θ x * (1 - firstOrderBlockCompletion θ x) at h1
  change (deriv (deriv firstOrderCompletion) q) ^ 2 ≤
    2822400 * firstOrderBlockCompletion θ x * (1 - firstOrderBlockCompletion θ x) at h2
  nlinarith

end
end SampleReuse
