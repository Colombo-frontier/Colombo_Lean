import NCConcave16991.GlobalHardStateLocalization

/-! # Actual low/high classification and exclusion of a low-high inversion -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem localStateDerivative_abs_le_gradient (v b : E) (previous next entry nextEntry nextExit : ℝ) (s u : E) :
    |localStateDerivative v b previous next entry nextEntry nextExit s u| ≤
      ‖gradient (localStateObjective v b previous next entry nextEntry nextExit) s‖ * ‖u‖ := by
  have hn := (InnerProductSpace.toDual ℝ E).norm_map
    (gradient (localStateObjective v b previous next entry nextEntry nextExit) s)
  rw [toDual_gradient, localStateObjective_fderiv] at hn
  have hh := (localStateDerivative v b previous next entry nextEntry nextExit s).le_opNorm u
  simpa only [Real.norm_eq_abs, hn] using hh

theorem localStateDerivative_source_eq (v b : E) (hv : ‖v‖ = 1)
    (previous next entry nextEntry nextExit : ℝ) (s : E) (hs : ‖s‖ ≤ 10) :
    localStateDerivative v b previous next entry nextEntry nextExit s v =
      netStateDerivative (stateScore v s) +
        incomingScoreDerivative previous (stateScore v s) entry (exitPair s b) +
        outgoingScoreDerivative (stateScore v s) next nextEntry nextExit -
        activationLoad previous (stateScore v s) * ⟪radialCap 21 b, v⟫_ℝ := by
  have hcap := radialCap_fderiv_identity (by norm_num : (0 : ℝ) < 10) s hs
  have ht : fderiv ℝ (stateScore v) s = innerSL ℝ v := by
    change fderiv ℝ (fun z ↦ ⟪v, radialCap 10 z⟫_ℝ) s = _
    rw [radialScore_fderiv (by norm_num : (0 : ℝ) < 10), hcap, ContinuousLinearMap.comp_id]
  have hval : ⟪s, v⟫_ℝ = stateScore v s := by
    rw [stateScore, radialCap_identity (by norm_num : (0 : ℝ) < 10) hs]
    exact real_inner_comm _ _
  have hself : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  simp only [localStateDerivative, add_apply, sub_apply, smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, ht, hcap, ContinuousLinearMap.id_apply, hval, hself, mul_one]
  dsimp [stateScoreCoefficient, netStateDerivative]
  ring

theorem localStateExit_source_abs_bound (v b : E) (hv : ‖v‖ = 1) (previous current : ℝ) :
    |activationLoad previous current * ⟪radialCap 21 b, v⟫_ℝ| ≤ 42 := by
  have hb := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 21) b).trans (min_le_right _ _)
  norm_num at hb
  have hi : |⟪radialCap 21 b, v⟫_ℝ| ≤ 42 := by
    have hh := abs_real_inner_le_norm (radialCap 21 b) v
    rw [hv, mul_one] at hh
    exact hh.trans hb
  have hL := activationLoad_bounds previous current
  exact (abs_product_bound _ _ 1 42 (by norm_num)
    (by rw [abs_of_nonneg hL.1]; exact hL.2) hi).trans_eq (by norm_num)

/-- Small actual local state gradient forces the source's low/high regimes. -/
theorem localStateObjective_classification (v b : E) (hv : ‖v‖ = 1)
    (previous next entry nextEntry nextExit : ℝ) (s : E)
    (he : |entry| ≤ 42) (he' : |nextEntry| ≤ 42) (hx' : |nextExit| ≤ 840)
    (hg : ‖gradient (localStateObjective v b previous next entry nextEntry nextExit) s‖ ≤ 1 / 20) :
    (-1 / 10 < stateScore v s ∧ stateScore v s ≤ 1 / 5) ∨ 1 ≤ stateScore v s := by
  by_cases hh : 1 ≤ stateScore v s
  · exact Or.inr hh
  have ht : stateScore v s ≤ 1 := (lt_of_not_ge hh).le
  have hs := localStateObjective_low_state_localized v b previous next entry nextEntry nextExit s he he' hx' ht hg
  have hd := localStateDerivative_abs_le_gradient v b previous next entry nextEntry nextExit s v
  rw [hv, mul_one] at hd
  have hd0 := (abs_le.mp (hd.trans hg)).1
  have hEq := localStateDerivative_source_eq v b hv previous next entry nextEntry nextExit s hs.le
  have hExit := (abs_le.mp (localStateExit_source_abs_bound v b hv previous (stateScore v s))).1
  left
  constructor
  · by_contra hn
    have hn' : stateScore v s ≤ -1 / 10 := le_of_not_gt hn
    have hNet := netStateDerivative_negative (by linarith : stateScore v s ≤ 0)
    have hC := totalScoreDerivative_low_nonpos previous (stateScore v s) next entry (exitPair s b) nextEntry nextExit (by linarith)
    rw [hNet] at hEq
    norm_num [gamma] at hEq
    nlinarith
  · by_contra hn
    have hn' : 1 / 5 ≤ stateScore v s := (lt_of_not_ge hn).le
    have hNet := netStateDerivative_middle hn' ht
    have hC := (abs_le.mp (totalScoreDerivative_abs_bound previous (stateScore v s) next entry (exitPair s b)
      nextEntry nextExit he (exitPair_abs_bound s b) he' hx')).2
    rw [hNet] at hEq
    norm_num [radialSlope] at hEq
    nlinarith

/-- A low state immediately before a high state contradicts a small actual
state gradient, with no connector/interiority assumption. -/
theorem localStateObjective_no_low_high (v b : E) (hv : ‖v‖ = 1)
    (previous next entry nextEntry nextExit : ℝ) (s : E)
    (he : |entry| ≤ 42) (he' : |nextEntry| ≤ 42) (hx' : |nextExit| ≤ 840)
    (hl : -1 / 10 < stateScore v s) (ht : stateScore v s ≤ 1 / 5) (hn : 1 ≤ next)
    (hg : ‖gradient (localStateObjective v b previous next entry nextEntry nextExit) s‖ ≤ 1 / 20) : False := by
  have hs := localStateObjective_low_state_localized v b previous next entry nextEntry nextExit s he he' hx' (by linarith) hg
  have hd := localStateDerivative_abs_le_gradient v b previous next entry nextEntry nextExit s v
  rw [hv, mul_one] at hd
  have hd0 := (abs_le.mp (hd.trans hg)).1
  have hEq := localStateDerivative_source_eq v b hv previous next entry nextEntry nextExit s hs.le
  have hC := totalScoreDerivative_low_high previous (stateScore v s) next entry (exitPair s b) nextEntry nextExit hl.le ht hn
  have hNet := netStateDerivative_upper (stateScore v s)
  have hExit := (abs_le.mp (localStateExit_source_abs_bound v b hv previous (stateScore v s))).1
  have hEq' : localStateDerivative v b previous next entry nextEntry nextExit s v =
      netStateDerivative (stateScore v s) - stateWeight - activationLoad previous (stateScore v s) * ⟪radialCap 21 b, v⟫_ℝ := by
    nlinarith only [hEq, hC]
  norm_num [stateWeight] at hEq'
  nlinarith

end

end NCConcave16991.GlobalHard
