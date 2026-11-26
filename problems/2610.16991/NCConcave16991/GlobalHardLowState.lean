import NCConcave16991.GlobalHardStateClassification

/-! # The actual low-state norm bound before connector or dual control -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem localStateDerivative_inside_apply (v b : E) (previous next entry nextEntry nextExit : ℝ)
    (s w : E) (hs : ‖s‖ ≤ 10) :
    localStateDerivative v b previous next entry nextEntry nextExit s w = gamma * ⟪s, w⟫_ℝ +
      stateScoreCoefficient previous (stateScore v s) next entry (exitPair s b) nextEntry nextExit * ⟪v, w⟫_ℝ -
      activationLoad previous (stateScore v s) * ⟪radialCap 21 b, w⟫_ℝ := by
  have hcap := radialCap_fderiv_identity (by norm_num : (0 : ℝ) < 10) s hs
  have ht : fderiv ℝ (stateScore v) s = innerSL ℝ v := by
    change fderiv ℝ (fun z ↦ ⟪v, radialCap 10 z⟫_ℝ) s = _
    rw [radialScore_fderiv (by norm_num : (0 : ℝ) < 10), hcap, ContinuousLinearMap.comp_id]
  simp only [localStateDerivative, add_apply, sub_apply, smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, ht, hcap, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- Every low state has norm below1/4. This follows from the actual
orthogonal derivative and bounded public exit, before any connector bound. -/
theorem localStateObjective_low_norm (v b : E) (hv : ‖v‖ = 1)
    (previous next entry nextEntry nextExit : ℝ) (s : E)
    (he : |entry| ≤ 42) (he' : |nextEntry| ≤ 42) (hx' : |nextExit| ≤ 840)
    (hl : -1 / 10 < stateScore v s) (ht : stateScore v s ≤ 1 / 5)
    (hg : ‖gradient (localStateObjective v b previous next entry nextEntry nextExit) s‖ ≤ 1 / 20) :
    ‖s‖ < 1 / 4 := by
  have hs := localStateObjective_low_state_localized v b previous next entry nextEntry nextExit s he he' hx' (by linarith) hg
  let t := stateScore v s
  let w := s - t • v
  have hvs : ⟪v, s⟫_ℝ = t := by
    dsimp [t]
    rw [stateScore, radialCap_identity (by norm_num : (0 : ℝ) < 10) hs.le]
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hvw : ⟪v, w⟫_ℝ = 0 := by
    dsimp [w]
    rw [inner_sub_right, real_inner_smul_right, hvv, hvs]
    ring
  have hsw : ⟪s, w⟫_ℝ = ‖w‖ ^ 2 := by
    have hh : ⟪s - t • v, w⟫_ℝ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
    rw [inner_sub_left, real_inner_smul_left, hvw, mul_zero, sub_zero] at hh
    exact hh
  have hd := localStateDerivative_abs_le_gradient v b previous next entry nextEntry nextExit s w
  have hd' := (abs_le.mp (hd.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg w)))).2
  have hEq := localStateDerivative_inside_apply v b previous next entry nextEntry nextExit s w hs.le
  rw [hsw, hvw, mul_zero, add_zero] at hEq
  have hb := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 21) b).trans (min_le_right _ _)
  norm_num at hb
  have hi : |⟪radialCap 21 b, w⟫_ℝ| ≤ 42 * ‖w‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg w))
  have hL := activationLoad_bounds previous t
  have hex := abs_product_bound (activationLoad previous t) ⟪radialCap 21 b, w⟫_ℝ 1 (42 * ‖w‖)
    (by norm_num) (by rw [abs_of_nonneg hL.1]; exact hL.2) hi
  have hex' := (abs_le.mp hex).2
  have hwsmall : ‖w‖ < 1 / 100 := by
    by_contra hnot
    have hge : 1 / 100 ≤ ‖w‖ := le_of_not_gt hnot
    have hp := mul_nonneg (sub_nonneg.mpr hge) (norm_nonneg w)
    norm_num [gamma] at hEq
    nlinarith
  have htsv : ⟪s, v⟫_ℝ = t := by rw [real_inner_comm]; exact hvs
  have hwNorm : ‖w‖ ^ 2 = ‖s‖ ^ 2 - t ^ 2 := by
    dsimp [w]
    rw [norm_sub_sq_real, norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, htsv]
    ring
  have htAbs : |t| ≤ 1 / 5 := by rw [abs_le]; constructor <;> dsimp [t] <;> linarith
  have htSq := (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1 / 5)).mpr htAbs
  have hwSq := (sq_lt_sq₀ (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1 / 100)).mpr hwsmall
  norm_num only [sq_abs] at htSq
  nlinarith [norm_nonneg s]

end

end NCConcave16991.GlobalHard
