import NCConcave16991.GlobalHardActivation
import NCConcave16991.LocalizationHessian

/-! # Literal globally capped outer stage and its unconditional value bounds -/

namespace NCConcave16991.GlobalHard

noncomputable section

open Set LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace ContDiff

def precedingFactor (t : ℝ) : ℝ := (1 - stateClamp t) * (1 - gate t)

theorem precedingFactor_nonneg (t : ℝ) : 0 ≤ precedingFactor t := by
  by_cases ht : 1 ≤ t
  · simp [precedingFactor, gate_one ht]
  · have he : stateClamp t ≤ 1 := by
      have hh := stateClamp_monotone (le_of_not_ge ht)
      rw [stateClamp_identity (by norm_num : (-2 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)] at hh
      exact hh
    exact mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr (gate_le_one t))

theorem precedingFactor_abs_bound (t : ℝ) : |precedingFactor t| ≤ 7 / 2 := by
  have he := stateClamp_abs_bound t
  have hg0 := gate_nonneg t
  have hg1 := gate_le_one t
  have hleft : |1 - stateClamp t| ≤ 7 / 2 := by
    have hh := abs_sub (1 : ℝ) (stateClamp t)
    norm_num at hh
    linarith
  have hright : |1 - gate t| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  rw [precedingFactor, abs_mul]
  exact (mul_le_mul hleft hright (abs_nonneg _) (by norm_num)).trans_eq (by ring)

def activationLoad (previous current : ℝ) : ℝ := gate previous * (1 - gate current)

theorem activationLoad_bounds (previous current : ℝ) :
    0 ≤ activationLoad previous current ∧ activationLoad previous current ≤ 1 := by
  have hp0 := gate_nonneg previous
  have hp1 := gate_le_one previous
  have hc0 := gate_nonneg current
  have hc1 := gate_le_one current
  dsimp [activationLoad]
  exact ⟨mul_nonneg hp0 (by linarith), by nlinarith⟩

variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]

def stateScore (v s : B) : ℝ := ⟪v, radialCap 10 s⟫_ℝ
def statePenalty (v s : B) : ℝ :=
  gamma / 2 * ‖s‖ ^ 2 - gamma / 2 * activationSq (stateScore v s) + statePotential (stateScore v s)

def entrance (u : A) (previous current : ℝ) (a : A) : ℝ :=
  -4 * activationLoad previous current * ⟪u, radialCap 21 a⟫_ℝ

def exit (previous current : ℝ) (s b : B) : ℝ :=
  -activationLoad previous current * ⟪radialCap 10 s, radialCap 21 b⟫_ℝ

def stateCoupling (previous current : ℝ) : ℝ := stateWeight * gate current * precedingFactor previous

/-- All four source terms, including the public vector exit rather than a
rank-one source projection. The preceding score is supplied by the previous stage. -/
def outerStage (u : A) (v : B) (previous : ℝ) (s : B) (a : A) (b : B) : ℝ :=
  entrance u previous (stateScore v s) a + exit previous (stateScore v s) s b +
    stateCoupling previous (stateScore v s) + statePenalty v s

theorem stateScore_abs_le (v : B) (hv : ‖v‖ = 1) (s : B) : |stateScore v s| ≤ ‖s‖ := by
  have hh := abs_real_inner_le_norm v (radialCap 10 s)
  rw [hv, one_mul] at hh
  exact hh.trans ((radialCap_value_bounds (by norm_num : (0 : ℝ) < 10) s).trans (min_le_left _ _))

theorem stateScore_cap_bound (v : B) (hv : ‖v‖ = 1) (s : B) : |stateScore v s| ≤ 20 := by
  have hh := abs_real_inner_le_norm v (radialCap 10 s)
  rw [hv, one_mul] at hh
  have hc := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 10) s).trans (min_le_right _ _)
  norm_num at hc
  exact hh.trans hc

theorem statePenalty_lower (v : B) (hv : ‖v‖ = 1) (s : B) :
    -(9 / 10) * radialSlope ≤ statePenalty v s := by
  have hh := (activation_abs_le (stateScore v s)).trans (stateScore_abs_le v hv s)
  have hs : activationSq (stateScore v s) ≤ ‖s‖ ^ 2 := by
    dsimp [activationSq]
    have hp := pow_le_pow_left₀ (abs_nonneg _) hh 2
    simpa only [sq_abs] using hp
  have hV := (statePotential_bounds (stateScore v s)).1
  dsimp [statePenalty, gamma]
  linarith

theorem entrance_abs_bound (u : A) (hu : ‖u‖ = 1) (previous current : ℝ) (a : A) :
    |entrance u previous current a| ≤ 168 := by
  have hl := activationLoad_bounds previous current
  have hi := abs_real_inner_le_norm u (radialCap 21 a)
  rw [hu, one_mul] at hi
  have hc := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 21) a).trans (min_le_right _ _)
  norm_num at hc
  have hb : |⟪u, radialCap 21 a⟫_ℝ| ≤ 42 := hi.trans hc
  have hm := mul_le_mul hl.2 hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [entrance, abs_mul, abs_mul, abs_of_nonneg hl.1]
  norm_num
  nlinarith

theorem exit_abs_bound (previous current : ℝ) (s b : B) : |exit previous current s b| ≤ 840 := by
  have hl := activationLoad_bounds previous current
  have hs := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 10) s).trans (min_le_right _ _)
  have hb := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 21) b).trans (min_le_right _ _)
  norm_num at hs hb
  have hi := (abs_real_inner_le_norm (radialCap 10 s) (radialCap 21 b)).trans
    (mul_le_mul hs hb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 20))
  have hm := mul_le_mul hl.2 hi (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [exit, abs_mul, abs_neg, abs_of_nonneg hl.1]
  nlinarith

theorem stateCoupling_nonneg (previous current : ℝ) : 0 ≤ stateCoupling previous current := by
  exact mul_nonneg (mul_nonneg (by norm_num [stateWeight]) (gate_nonneg current))
    (precedingFactor_nonneg previous)

/-- This is the uniform source lower bound for the literal outer stage, with
no gradient, connector-radius or dual-interiority assumption. -/
theorem outerStage_lower (u : A) (hu : ‖u‖ = 1) (v : B) (hv : ‖v‖ = 1)
    (previous : ℝ) (s : B) (a : A) (b : B) : -31000 ≤ outerStage u v previous s a b := by
  have he := (abs_le.mp (entrance_abs_bound u hu previous (stateScore v s) a)).1
  have hx := (abs_le.mp (exit_abs_bound previous (stateScore v s) s b)).1
  have hg := stateCoupling_nonneg previous (stateScore v s)
  have hp := statePenalty_lower v hv s
  dsimp [outerStage]
  norm_num [radialSlope] at hp
  linarith

theorem statePenalty_zero (v : B) : statePenalty v 0 = 0 := by
  have hs : stateScore v 0 = 0 := by simp [stateScore, radialCap_zero]
  rw [statePenalty, hs, activationSq, activation_zero (by norm_num [deltaGate] : (0 : ℝ) ≤ deltaGate),
    statePotential_left (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  simp

theorem outerStage_zero (u : A) (v : B) (previous : ℝ) : outerStage u v previous 0 0 0 = 0 := by
  have hs : stateScore v 0 = 0 := by simp [stateScore, radialCap_zero]
  simp [outerStage, entrance, exit, stateCoupling, hs, radialCap_zero,
    gate_zero (by norm_num : (0 : ℝ) ≤ 1 / 5), statePenalty_zero]

end

end NCConcave16991.GlobalHard
