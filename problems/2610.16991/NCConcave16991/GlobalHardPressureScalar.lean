import NCConcave16991.GlobalHardStage

/-! # Actual scalar pressure bounds for state classification -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationStepSecond

theorem statePotentialDerivative_left {t : ℝ} (ht : t ≤ 1 / 10) : statePotentialDerivative t = 0 := by
  have h1 : 10 * t - 1 ≤ 0 := by linarith
  have h2 : 10 * t - 10 ≤ 0 := by linarith
  simp [statePotentialDerivative, Real.smoothTransition.zero_of_nonpos h1,
    Real.smoothTransition.zero_of_nonpos h2]

theorem statePotentialDerivative_middle {t : ℝ} (hl : 1 / 5 ≤ t) (hr : t ≤ 1) :
    statePotentialDerivative t = -radialSlope := by
  have h1 : 1 ≤ 10 * t - 1 := by linarith
  have h2 : 10 * t - 10 ≤ 0 := by linarith
  simp [statePotentialDerivative, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.zero_of_nonpos h2]

theorem gateDerivative_zero {t : ℝ} (ht : t ≤ 1 / 5 ∨ 1 ≤ t) : deriv gate t = 0 := by
  rcases ht with ht | ht
  · exact (gate_hasDerivAt_zero ht).deriv
  · exact (gate_hasDerivAt_one ht).deriv

theorem weighted_gateDerivative_abs_bound (t : ℝ) : |t * deriv gate t| ≤ 10 := by
  by_cases hl : t ≤ 1 / 5
  · rw [gateDerivative_zero (Or.inl hl)]; norm_num
  · by_cases hr : 1 ≤ t
    · rw [gateDerivative_zero (Or.inr hr)]; norm_num
    · have ht : |t| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
      have hd : |deriv gate t| ≤ 10 := by rw [abs_of_nonneg (gate_deriv_bound t).1]; exact (gate_deriv_bound t).2
      rw [abs_mul]
      exact (mul_le_mul ht hd (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem stateClampDerivative_left {t : ℝ} (ht : t ≤ -3) : stateClampDerivative t = 0 := by
  have h1 : t + 3 ≤ 0 := by linarith
  have h2 : t - 2 ≤ 0 := by linarith
  simp [stateClampDerivative, Real.smoothTransition.zero_of_nonpos h1,
    Real.smoothTransition.zero_of_nonpos h2]

theorem stateClampDerivative_right {t : ℝ} (ht : 3 ≤ t) : stateClampDerivative t = 0 := by
  have h1 : 1 ≤ t + 3 := by linarith
  have h2 : 1 ≤ t - 2 := by linarith
  simp [stateClampDerivative, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2]

theorem weighted_stateClampDerivative_abs_bound (t : ℝ) : |t * stateClampDerivative t| ≤ 3 := by
  by_cases hl : t ≤ -3
  · rw [stateClampDerivative_left hl]; norm_num
  · by_cases hr : 3 ≤ t
    · rw [stateClampDerivative_right hr]; norm_num
    · have ht : |t| ≤ 3 := by rw [abs_le]; constructor <;> linarith
      have hd : |stateClampDerivative t| ≤ 1 := by
        rw [abs_of_nonneg (stateClampDerivative_bounds t).1]
        exact (stateClampDerivative_bounds t).2
      rw [abs_mul]
      exact (mul_le_mul ht hd (abs_nonneg _) (by norm_num)).trans_eq (by ring)

def netStateDerivative (t : ℝ) : ℝ :=
  gamma * t - gamma * activation t * activationDerivative t + statePotentialDerivative t

/-- The low-state scalar penalty has its source's uniform upper bound 1/50,
derived from the literal delayed activation and potential. -/
theorem netStateDerivative_upper (t : ℝ) : netStateDerivative t ≤ 1 / 50 := by
  by_cases ht : t ≤ 0
  · have hz : t ≤ deltaGate := ht.trans deltaGate_pos.le
    rw [netStateDerivative, activation_zero hz, statePotentialDerivative_left (by linarith)]
    norm_num [gamma]
    linarith
  · by_cases hhigh : 2 * deltaGate ≤ t
    · rw [netStateDerivative, activation_eq_self hhigh, activationDerivative_one hhigh]
      have hV := (statePotentialDerivative_bounds t).2
      nlinarith
    · have hhh := mul_nonneg (activation_bounds t).1 (activationDerivative_bounds t).1
      have hV := (statePotentialDerivative_bounds t).2
      dsimp [netStateDerivative, gamma]
      have htop : t ≤ 2 / 430000 := by
        have hh := le_of_lt (lt_of_not_ge hhigh)
        norm_num [deltaGate] at hh ⊢
        exact hh
      nlinarith

theorem netStateDerivative_negative {t : ℝ} (ht : t ≤ 0) : netStateDerivative t = gamma * t := by
  have hz : t ≤ deltaGate := ht.trans deltaGate_pos.le
  rw [netStateDerivative, activation_zero hz, statePotentialDerivative_left (by linarith)]
  ring

theorem netStateDerivative_middle {t : ℝ} (hl : 1 / 5 ≤ t) (hr : t ≤ 1) :
    netStateDerivative t = -radialSlope := by
  have hh : 2 * deltaGate ≤ t := by norm_num [deltaGate] at *; linarith
  rw [netStateDerivative, activation_eq_self hh, activationDerivative_one hh, statePotentialDerivative_middle hl hr]
  ring

theorem weighted_activation_product_bound {t : ℝ} (ht : t ≤ 1) :
    |t * activation t * activationDerivative t| ≤ 17 := by
  by_cases hl : t ≤ 0
  · rw [activation_zero (hl.trans deltaGate_pos.le)]; norm_num
  · have ht0 : 0 ≤ t := (lt_of_not_ge hl).le
    have hh0 := (activation_bounds t).1
    have hh1 : activation t ≤ 1 := by
      have hh := (activation_bounds t).2
      rw [max_eq_left ht0] at hh
      exact hh.trans ht
    have hd0 := (activationDerivative_bounds t).1
    have hd1 := (activationDerivative_bounds t).2
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg ht0 hh0) hd0)]
    have hm := mul_le_mul ht hh1 hh0 (by norm_num : (0 : ℝ) ≤ 1)
    have hp := mul_le_mul hm hd1 hd0 (by norm_num : (0 : ℝ) ≤ 1 * 1)
    norm_num at hp
    exact hp

end

end NCConcave16991.GlobalHard
