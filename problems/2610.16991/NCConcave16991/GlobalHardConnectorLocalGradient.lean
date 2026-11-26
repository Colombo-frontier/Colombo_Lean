import NCConcave16991.GlobalHardStateGradient
import NCConcave16991.LocalizationHessian

/-! # Actual connector-ray derivatives of the public outer stage -/

namespace NCConcave16991.GlobalHard
noncomputable section
open LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

variable {A E : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def outerConnectorDerivative (u : A) (v : E) (previous : ℝ) (s : E) (a : A) (b : E) : ℝ :=
  -4 * activationLoad previous (stateScore v s) * ⟪u, fderiv ℝ (radialCap 21) a a⟫_ℝ -
    activationLoad previous (stateScore v s) * ⟪radialCap 10 s, fderiv ℝ (radialCap 21) b b⟫_ℝ

theorem radialCap_ray_hasDerivAt {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {C : ℝ} (hC : 0 < C) (a : F) :
    HasDerivAt (fun t : ℝ ↦ radialCap C (t • a)) (fderiv ℝ (radialCap C) a a) 1 := by
  have hc : HasFDerivAt (radialCap C) (fderiv ℝ (radialCap C) a) ((1 : ℝ) • a) := by
    simpa using (radialCap_differentiable hC a).hasFDerivAt
  convert hc.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const a) using 1 <;> first | rfl | simp only [one_smul]

theorem outerStage_connector_ray_hasDerivAt (u : A) (v : E) (previous : ℝ) (s : E) (a : A) (b : E) :
    HasDerivAt (fun t : ℝ ↦ outerStage u v previous s (t • a) (t • b))
      (outerConnectorDerivative u v previous s a b) 1 := by
  have ha := (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt 1
    (radialCap_ray_hasDerivAt (by norm_num : (0 : ℝ) < 21) a)
  have hb := (innerSL ℝ (radialCap 10 s)).hasFDerivAt.comp_hasDerivAt 1
    (radialCap_ray_hasDerivAt (by norm_num : (0 : ℝ) < 21) b)
  have hh := (((hasDerivAt_const (1 : ℝ) (statePenalty v s)).add
    (ha.const_mul (-4 * activationLoad previous (stateScore v s)))).sub
    (hb.const_mul (activationLoad previous (stateScore v s)))).add_const
      (stateCoupling previous (stateScore v s))
  convert hh using 1
  · funext t
    simp only [outerStage, entrance, exit, innerSL_apply_apply, Function.comp_apply,
      Pi.add_apply, Pi.sub_apply]
    ring
  · simp only [outerConnectorDerivative, innerSL_apply_apply]
    ring

theorem outerConnectorDerivative_zero (u : A) (v : E) (previous : ℝ) (s : E) (a : A) (b : E)
    (h : activationLoad previous (stateScore v s) = 0) :
    outerConnectorDerivative u v previous s a b = 0 := by simp [outerConnectorDerivative, h]

theorem outerConnectorDerivative_abs_bound (u : A) (v : E) (hu : ‖u‖ = 1)
    (previous : ℝ) (s : E) (a : A) (b : E) (hs : ‖s‖ ≤ 1 / 4) :
    |outerConnectorDerivative u v previous s a b| ≤
      (17 / 4 : ℝ) * ‖WithLp.toLp 2 (a, b)‖ := by
  have ha : ‖fderiv ℝ (radialCap 21) a a‖ ≤ ‖a‖ := by
    exact ((fderiv ℝ (radialCap 21) a).le_opNorm a).trans
      ((mul_le_mul_of_nonneg_right (radialCap_fderiv_norm_le (by norm_num : (0 : ℝ) < 21) a) (norm_nonneg a)).trans_eq (one_mul _))
  have hb : ‖fderiv ℝ (radialCap 21) b b‖ ≤ ‖b‖ := by
    exact ((fderiv ℝ (radialCap 21) b).le_opNorm b).trans
      ((mul_le_mul_of_nonneg_right (radialCap_fderiv_norm_le (by norm_num : (0 : ℝ) < 21) b) (norm_nonneg b)).trans_eq (one_mul _))
  have hs' : ‖radialCap 10 s‖ ≤ 1 / 4 :=
    ((radialCap_value_bounds (by norm_num : (0 : ℝ) < 10) s).trans (min_le_left _ _)).trans hs
  have hiA : |⟪u, fderiv ℝ (radialCap 21) a a⟫_ℝ| ≤ ‖a‖ := by
    simpa only [hu, one_mul] using (abs_real_inner_le_norm u (fderiv ℝ (radialCap 21) a a)).trans
      (mul_le_mul_of_nonneg_left ha (norm_nonneg u))
  have hiB : |⟪radialCap 10 s, fderiv ℝ (radialCap 21) b b⟫_ℝ| ≤ 1 / 4 * ‖b‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hs' hb (norm_nonneg _) (by norm_num))
  have hL := activationLoad_bounds previous (stateScore v s)
  have hLA : |-4 * activationLoad previous (stateScore v s)| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg hL.1]
    norm_num
    linarith
  have hLB : |activationLoad previous (stateScore v s)| ≤ 1 := by rw [abs_of_nonneg hL.1]; exact hL.2
  have h1 := abs_product_bound _ _ 4 ‖a‖ (by norm_num) hLA hiA
  have h2 := abs_product_bound _ _ 1 (1 / 4 * ‖b‖) (by norm_num) hLB hiB
  have habA := WithLp.norm_fst_le (p := 2) (α := A) (β := E) (WithLp.toLp 2 (a, b))
  have habB := WithLp.norm_snd_le (p := 2) (α := A) (β := E) (WithLp.toLp 2 (a, b))
  have hh := abs_sub (-4 * activationLoad previous (stateScore v s) * ⟪u, fderiv ℝ (radialCap 21) a a⟫_ℝ)
    (activationLoad previous (stateScore v s) * ⟪radialCap 10 s, fderiv ℝ (radialCap 21) b b⟫_ℝ)
  dsimp [outerConnectorDerivative]
  change ‖a‖ ≤ ‖WithLp.toLp 2 (a, b)‖ at habA
  change ‖b‖ ≤ ‖WithLp.toLp 2 (a, b)‖ at habB
  nlinarith

end
end NCConcave16991.GlobalHard
