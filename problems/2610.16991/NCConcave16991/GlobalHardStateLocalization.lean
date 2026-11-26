import NCConcave16991.GlobalHardStateGradient

/-! # Low scores cannot hide outside the actual radial identity region -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exitPair_abs_bound (s b : E) : |exitPair s b| ≤ 840 := by
  have hb := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 21) b).trans (min_le_right _ _)
  have hs := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 10) s).trans (min_le_right _ _)
  norm_num at hb hs
  exact (abs_real_inner_le_norm _ _).trans (by nlinarith [mul_le_mul hb hs (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 42)])

theorem radialCap_radial_derivative (C : ℝ) (s : E) (hs : s ≠ 0) :
    fderiv ℝ (radialCap C) s (unitDirection s) = radialSpeed C ‖s‖ • unitDirection s := by
  have hu : ⟪unitDirection s, unitDirection s⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_unitDirection hs]
    norm_num
  rw [(radialCap_hasFDerivAt_of_ne_zero hs).fderiv, radialOperator_apply, hu]
  simp only [mul_one]
  module

theorem stateScore_radial_derivative (v s : E) (hs : s ≠ 0) (hr : 10 ≤ ‖s‖) :
    fderiv ℝ (stateScore v) s (unitDirection s) =
      radialSpeed 10 ‖s‖ * stateScore v s / radialLength 10 ‖s‖ := by
  have hf : 0 < radialLength 10 ‖s‖ :=
    (by norm_num : (0 : ℝ) < 10).trans_le (radialLength_ge_cap (by norm_num) hr)
  have hc : radialCap 10 s = radialLength 10 ‖s‖ • unitDirection s := by
    simp [radialCap, unitDirection, smul_smul, div_eq_mul_inv]
  have ht : stateScore v s = radialLength 10 ‖s‖ * ⟪v, unitDirection s⟫_ℝ := by
    rw [stateScore, hc, real_inner_smul_right]
  change fderiv ℝ (fun z ↦ ⟪v, radialCap 10 z⟫_ℝ) s (unitDirection s) = _
  rw [radialScore_fderiv (by norm_num : (0 : ℝ) < 10)]
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, radialCap_radial_derivative 10 s hs,
    real_inner_smul_right]
  rw [ht]
  field_simp [hf.ne'] <;> ring

variable [CompleteSpace E]

/-- Actual local state localization, before any connector bound or any
assertion that the unconstrained dual optimizer is feasible. -/
theorem localStateObjective_low_state_localized (v b : E) (previous next entry nextEntry nextExit : ℝ) (s : E)
    (he : |entry| ≤ 42) (he' : |nextEntry| ≤ 42) (hx' : |nextExit| ≤ 840)
    (ht : stateScore v s ≤ 1)
    (hg : ‖gradient (localStateObjective v b previous next entry nextEntry nextExit) s‖ ≤ 1 / 20) :
    ‖s‖ < 10 := by
  by_contra hnot
  have hr : 10 ≤ ‖s‖ := le_of_not_gt hnot
  have hs : s ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 10).trans_le hr)
  let u := unitDirection s
  let f := radialLength 10 ‖s‖
  let speed := radialSpeed 10 ‖s‖
  let t := stateScore v s
  let B := stateScoreCoefficient previous t next entry (exitPair s b) nextEntry nextExit
  let L := activationLoad previous t
  have hu : ‖u‖ = 1 := norm_unitDirection hs
  have hf : 10 ≤ f := radialLength_ge_cap (by norm_num) hr
  have hfpos : 0 < f := (by norm_num : (0 : ℝ) < 10).trans_le hf
  have hspeed0 : 0 ≤ speed := radialSpeed_nonneg 10 _
  have hspeed1 : speed ≤ 1 := radialSpeed_le_one 10 _
  have hspeed : |speed| ≤ 1 := by rw [abs_of_nonneg hspeed0]; exact hspeed1
  have hB : |t * B| ≤ 138233 := weighted_stateScoreCoefficient_abs_bound
    previous t next entry (exitPair s b) nextEntry nextExit ht he (exitPair_abs_bound s b) he' hx'
  have hmidprod := abs_product_bound speed (t * B) 1 138233 (by norm_num) hspeed hB
  have hmid : -(138233 / 10 : ℝ) ≤ speed * (t * B) / f := by
    apply (le_div_iff₀ hfpos).mpr
    have hh := (abs_le.mp hmidprod).1
    nlinarith
  have hb := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 21) b).trans (min_le_right _ _)
  norm_num at hb
  have hib : |⟪radialCap 21 b, u⟫_ℝ| ≤ 42 := by
    have hh := abs_real_inner_le_norm (radialCap 21 b) u
    rw [hu, mul_one] at hh
    exact hh.trans hb
  have hL := activationLoad_bounds previous t
  have hLs : |L * speed| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hL.1, abs_of_nonneg hspeed0]
    exact (mul_le_mul hL.2 hspeed1 hspeed0 (by norm_num)).trans_eq (by ring)
  have hex := abs_product_bound (L * speed) ⟪radialCap 21 b, u⟫_ℝ 1 42 (by norm_num) hLs hib
  have hsu : ⟪s, u⟫_ℝ = ‖s‖ := by
    dsimp [u, unitDirection]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hs]
  have hdir : localStateDerivative v b previous next entry nextEntry nextExit s u =
      gamma * ‖s‖ + speed * (t * B) / f - (L * speed) * ⟪radialCap 21 b, u⟫_ℝ := by
    simp only [localStateDerivative, add_apply, sub_apply, smul_apply,
      innerSL_apply_apply, ContinuousLinearMap.comp_apply]
    rw [hsu, stateScore_radial_derivative v s hs hr, radialCap_radial_derivative 10 s hs, real_inner_smul_right]
    dsimp [speed, t, B, f, L, u]
    ring
  have hnorm := (InnerProductSpace.toDual ℝ E).norm_map
    (gradient (localStateObjective v b previous next entry nextEntry nextExit) s)
  rw [toDual_gradient, localStateObjective_fderiv] at hnorm
  have hop : ‖localStateDerivative v b previous next entry nextEntry nextExit s‖ ≤ 1 / 20 := by
    rw [hnorm]
    exact hg
  have hv := (localStateDerivative v b previous next entry nextEntry nextExit s).le_opNorm u
  rw [hu, mul_one, Real.norm_eq_abs] at hv
  have hval : localStateDerivative v b previous next entry nextEntry nextExit s u ≤ 1 / 20 :=
    (le_abs_self _).trans (hv.trans hop)
  rw [hdir] at hval
  have hx := (abs_le.mp hex).2
  norm_num [gamma] at hval
  nlinarith

end

end NCConcave16991.GlobalHard
