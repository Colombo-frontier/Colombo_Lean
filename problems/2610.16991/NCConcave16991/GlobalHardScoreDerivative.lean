import NCConcave16991.GlobalHardPressureScalar

/-! # Actual neighboring-stage score derivatives and source pressure constants -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationStepSecond

def precedingFactorDerivative (t : ℝ) : ℝ :=
  -stateClampDerivative t * (1 - gate t) - (1 - stateClamp t) * deriv gate t

theorem precedingFactor_hasDerivAt (t : ℝ) : HasDerivAt precedingFactor (precedingFactorDerivative t) t := by
  have hg := (gate_contDiff.differentiable (by simp) t).hasDerivAt
  have hh := ((hasDerivAt_const t 1).sub (stateClamp_hasDerivAt t)).mul ((hasDerivAt_const t 1).sub hg)
  convert hh using 1 <;> first | rfl | dsimp [precedingFactorDerivative]; ring

theorem abs_product_bound (a b A B : ℝ) (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

theorem one_sub_gate_abs_bound (t : ℝ) : |1 - gate t| ≤ 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (gate_le_one t))]
  linarith [gate_nonneg t]

theorem one_sub_stateClamp_abs_bound (t : ℝ) : |1 - stateClamp t| ≤ 7 / 2 := by
  have hh := abs_sub (1 : ℝ) (stateClamp t)
  norm_num at hh
  linarith [stateClamp_abs_bound t]

theorem gate_derivative_abs_bound (t : ℝ) : |deriv gate t| ≤ 10 := by
  rw [abs_of_nonneg (gate_deriv_bound t).1]
  exact (gate_deriv_bound t).2

theorem precedingFactorDerivative_abs_bound (t : ℝ) : |precedingFactorDerivative t| ≤ 36 := by
  have he : |-stateClampDerivative t| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (stateClampDerivative_bounds t).1]
    exact (stateClampDerivative_bounds t).2
  have h1 := abs_product_bound _ _ 1 1 (by norm_num) he (one_sub_gate_abs_bound t)
  have h2 := abs_product_bound _ _ (7 / 2) 10 (by norm_num) (one_sub_stateClamp_abs_bound t) (gate_derivative_abs_bound t)
  have hh := abs_sub (-stateClampDerivative t * (1 - gate t)) ((1 - stateClamp t) * deriv gate t)
  dsimp [precedingFactorDerivative]
  linarith

theorem weighted_precedingFactorDerivative_abs_bound (t : ℝ) : |t * precedingFactorDerivative t| ≤ 38 := by
  have he : |-(t * stateClampDerivative t)| ≤ 3 := by
    rw [abs_neg]
    exact weighted_stateClampDerivative_abs_bound t
  have h1 := abs_product_bound _ _ 3 1 (by norm_num) he (one_sub_gate_abs_bound t)
  have h2 := abs_product_bound _ _ (7 / 2) 10 (by norm_num) (one_sub_stateClamp_abs_bound t) (weighted_gateDerivative_abs_bound t)
  have hh := abs_sub (-(t * stateClampDerivative t) * (1 - gate t)) ((1 - stateClamp t) * (t * deriv gate t))
  have hEq : t * precedingFactorDerivative t =
      -(t * stateClampDerivative t) * (1 - gate t) - (1 - stateClamp t) * (t * deriv gate t) := by
    dsimp [precedingFactorDerivative]
    ring
  rw [hEq]
  linarith

def incomingScoreCoefficient (previous entry exitValue : ℝ) : ℝ :=
  4 * gate previous * entry + gate previous * exitValue + stateWeight * precedingFactor previous

def outgoingScoreCoefficient (next entry exitValue : ℝ) : ℝ :=
  -4 * (1 - gate next) * entry - (1 - gate next) * exitValue

def incomingScoreDerivative (previous current entry exitValue : ℝ) : ℝ :=
  incomingScoreCoefficient previous entry exitValue * deriv gate current

def outgoingScoreDerivative (current next entry exitValue : ℝ) : ℝ :=
  outgoingScoreCoefficient next entry exitValue * deriv gate current +
    stateWeight * gate next * precedingFactorDerivative current

def incomingScoreFunction (previous current entry exitValue : ℝ) : ℝ :=
  incomingScoreCoefficient previous entry exitValue * gate current - 4 * gate previous * entry - gate previous * exitValue

def outgoingScoreFunction (current next entry exitValue : ℝ) : ℝ :=
  outgoingScoreCoefficient next entry exitValue * gate current + stateWeight * gate next * precedingFactor current

theorem incomingScoreFunction_eq (previous current entry exitValue : ℝ) :
    incomingScoreFunction previous current entry exitValue =
      -4 * gate previous * (1 - gate current) * entry - gate previous * (1 - gate current) * exitValue +
        stateWeight * gate current * precedingFactor previous := by
  dsimp [incomingScoreFunction, incomingScoreCoefficient]
  ring

theorem outgoingScoreFunction_eq (current next entry exitValue : ℝ) :
    outgoingScoreFunction current next entry exitValue =
      -4 * gate current * (1 - gate next) * entry - gate current * (1 - gate next) * exitValue +
        stateWeight * gate next * precedingFactor current := by
  dsimp [outgoingScoreFunction, outgoingScoreCoefficient]
  ring

theorem incomingScoreFunction_hasDerivAt (previous current entry exitValue : ℝ) :
    HasDerivAt (fun t ↦ incomingScoreFunction previous t entry exitValue)
      (incomingScoreDerivative previous current entry exitValue) current := by
  have hq := (gate_contDiff.differentiable (by simp) current).hasDerivAt
  exact ((hq.const_mul (incomingScoreCoefficient previous entry exitValue)).sub_const
    (4 * gate previous * entry)).sub_const (gate previous * exitValue)

theorem outgoingScoreFunction_hasDerivAt (current next entry exitValue : ℝ) :
    HasDerivAt (fun t ↦ outgoingScoreFunction t next entry exitValue)
      (outgoingScoreDerivative current next entry exitValue) current := by
  have hq := (gate_contDiff.differentiable (by simp) current).hasDerivAt
  exact (hq.const_mul (outgoingScoreCoefficient next entry exitValue)).add
    ((precedingFactor_hasDerivAt current).const_mul (stateWeight * gate next))

theorem incomingScoreCoefficient_abs_bound (previous entry exitValue : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) : |incomingScoreCoefficient previous entry exitValue| ≤ 1610 := by
  have hg : |gate previous| ≤ 1 := by rw [abs_of_nonneg (gate_nonneg _)]; exact gate_le_one _
  have h1 := abs_product_bound _ _ 1 42 (by norm_num) hg he
  have h2 := abs_product_bound _ _ 1 840 (by norm_num) hg hx
  have h3 := abs_product_bound _ _ 172 (7 / 2) (by norm_num)
    (by norm_num [stateWeight] : |stateWeight| ≤ 172) (precedingFactor_abs_bound previous)
  have h4 : |4 * gate previous * entry| ≤ 168 := by
    have hh := abs_product_bound 4 (gate previous * entry) 4 42 (by norm_num) (by norm_num) (by simpa using h1)
    simpa only [mul_assoc] using hh.trans_eq (by norm_num)
  have ht := (abs_add_le (4 * gate previous * entry + gate previous * exitValue) (stateWeight * precedingFactor previous)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  dsimp [incomingScoreCoefficient]
  linarith

theorem outgoingScoreCoefficient_abs_bound (next entry exitValue : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) : |outgoingScoreCoefficient next entry exitValue| ≤ 1008 := by
  have h1 := abs_product_bound _ _ 1 42 (by norm_num) (one_sub_gate_abs_bound next) he
  have h2 := abs_product_bound _ _ 1 840 (by norm_num) (one_sub_gate_abs_bound next) hx
  have h3 : |-4 * (1 - gate next) * entry| ≤ 168 := by
    have hh := abs_product_bound (-4) ((1 - gate next) * entry) 4 42 (by norm_num) (by norm_num) (by simpa using h1)
    simpa only [mul_assoc] using hh.trans_eq (by norm_num)
  have ht := abs_sub (-4 * (1 - gate next) * entry) ((1 - gate next) * exitValue)
  dsimp [outgoingScoreCoefficient]
  linarith

theorem incomingScoreDerivative_abs_bound (previous current entry exitValue : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) : |incomingScoreDerivative previous current entry exitValue| ≤ 16100 := by
  exact (abs_product_bound _ _ 1610 10 (by norm_num) (incomingScoreCoefficient_abs_bound previous entry exitValue he hx)
    (gate_derivative_abs_bound current)).trans_eq (by norm_num)

theorem outgoingScoreDerivative_abs_bound (current next entry exitValue : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) : |outgoingScoreDerivative current next entry exitValue| ≤ 16272 := by
  have h1 := abs_product_bound _ _ 1008 10 (by norm_num) (outgoingScoreCoefficient_abs_bound next entry exitValue he hx)
    (gate_derivative_abs_bound current)
  have hg : |stateWeight * gate next| ≤ 172 := by
    have hh := abs_product_bound stateWeight (gate next) 172 1 (by norm_num) (by norm_num [stateWeight] : |stateWeight| ≤ 172)
      (by rw [abs_of_nonneg (gate_nonneg next)]; exact gate_le_one next)
    simpa using hh
  have h2 := abs_product_bound _ _ 172 36 (by norm_num) hg (precedingFactorDerivative_abs_bound current)
  have ht := abs_add_le (outgoingScoreCoefficient next entry exitValue * deriv gate current)
    (stateWeight * gate next * precedingFactorDerivative current)
  dsimp [outgoingScoreDerivative]
  linarith

theorem totalScoreDerivative_abs_bound (previous current next entry exitValue nextEntry nextExit : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) (he' : |nextEntry| ≤ 42) (hx' : |nextExit| ≤ 840) :
    |incomingScoreDerivative previous current entry exitValue + outgoingScoreDerivative current next nextEntry nextExit| ≤ 32372 := by
  exact (abs_add_le _ _).trans ((add_le_add (incomingScoreDerivative_abs_bound _ _ _ _ he hx)
    (outgoingScoreDerivative_abs_bound _ _ _ _ he' hx')).trans_eq (by norm_num))

theorem weighted_incomingScoreDerivative_abs_bound (previous current entry exitValue : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) :
    |current * incomingScoreDerivative previous current entry exitValue| ≤ 16100 := by
  have hh := abs_product_bound _ _ 1610 10 (by norm_num)
    (incomingScoreCoefficient_abs_bound previous entry exitValue he hx) (weighted_gateDerivative_abs_bound current)
  have heq : current * incomingScoreDerivative previous current entry exitValue =
      incomingScoreCoefficient previous entry exitValue * (current * deriv gate current) := by
    dsimp [incomingScoreDerivative]
    ring
  rw [heq]
  exact hh.trans_eq (by norm_num)

theorem weighted_outgoingScoreDerivative_abs_bound (current next entry exitValue : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) :
    |current * outgoingScoreDerivative current next entry exitValue| ≤ 16616 := by
  have h1 := abs_product_bound _ _ 1008 10 (by norm_num)
    (outgoingScoreCoefficient_abs_bound next entry exitValue he hx) (weighted_gateDerivative_abs_bound current)
  have hg : |stateWeight * gate next| ≤ 172 := by
    have hh := abs_product_bound stateWeight (gate next) 172 1 (by norm_num) (by norm_num [stateWeight] : |stateWeight| ≤ 172)
      (by rw [abs_of_nonneg (gate_nonneg next)]; exact gate_le_one next)
    simpa using hh
  have h2 := abs_product_bound _ _ 172 38 (by norm_num) hg (weighted_precedingFactorDerivative_abs_bound current)
  have ht := abs_add_le (outgoingScoreCoefficient next entry exitValue * (current * deriv gate current))
    (stateWeight * gate next * (current * precedingFactorDerivative current))
  have heq : current * outgoingScoreDerivative current next entry exitValue =
      outgoingScoreCoefficient next entry exitValue * (current * deriv gate current) +
        stateWeight * gate next * (current * precedingFactorDerivative current) := by
    dsimp [outgoingScoreDerivative]
    ring
  rw [heq]
  linarith

theorem weighted_totalScoreDerivative_abs_bound (previous current next entry exitValue nextEntry nextExit : ℝ)
    (he : |entry| ≤ 42) (hx : |exitValue| ≤ 840) (he' : |nextEntry| ≤ 42) (hx' : |nextExit| ≤ 840) :
    |current * (incomingScoreDerivative previous current entry exitValue + outgoingScoreDerivative current next nextEntry nextExit)| ≤ 32716 := by
  rw [mul_add]
  exact (abs_add_le _ _).trans ((add_le_add (weighted_incomingScoreDerivative_abs_bound _ _ _ _ he hx)
    (weighted_outgoingScoreDerivative_abs_bound _ _ _ _ he' hx')).trans_eq (by norm_num))

theorem stateClampDerivative_identity {t : ℝ} (hl : -2 ≤ t) (hr : t ≤ 2) : stateClampDerivative t = 1 := by
  have h1 : 1 ≤ t + 3 := by linarith
  have h2 : t - 2 ≤ 0 := by linarith
  simp [stateClampDerivative, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.zero_of_nonpos h2]

theorem incomingScoreDerivative_inactive (previous current entry exitValue : ℝ) (ht : current ≤ 1 / 5) :
    incomingScoreDerivative previous current entry exitValue = 0 := by
  simp [incomingScoreDerivative, gateDerivative_zero (Or.inl ht)]

theorem outgoingScoreDerivative_inactive (current next entry exitValue : ℝ) (ht : current ≤ 1 / 5) :
    outgoingScoreDerivative current next entry exitValue = -stateWeight * gate next * stateClampDerivative current := by
  simp only [outgoingScoreDerivative, precedingFactorDerivative, gate_zero ht,
    gateDerivative_zero (Or.inl ht), sub_zero, mul_zero, one_mul, mul_one, zero_add]
  ring

theorem totalScoreDerivative_low_nonpos (previous current next entry exitValue nextEntry nextExit : ℝ)
    (ht : current ≤ 1 / 5) :
    incomingScoreDerivative previous current entry exitValue + outgoingScoreDerivative current next nextEntry nextExit ≤ 0 := by
  rw [incomingScoreDerivative_inactive _ _ _ _ ht, outgoingScoreDerivative_inactive _ _ _ _ ht, zero_add]
  have hp := mul_nonneg (mul_nonneg (by norm_num [stateWeight] : 0 ≤ stateWeight) (gate_nonneg next))
    (stateClampDerivative_bounds current).1
  nlinarith

theorem totalScoreDerivative_low_high (previous current next entry exitValue nextEntry nextExit : ℝ)
    (hl : -1 / 10 ≤ current) (ht : current ≤ 1 / 5) (hn : 1 ≤ next) :
    incomingScoreDerivative previous current entry exitValue + outgoingScoreDerivative current next nextEntry nextExit = -stateWeight := by
  rw [incomingScoreDerivative_inactive _ _ _ _ ht, outgoingScoreDerivative_inactive _ _ _ _ ht,
    gate_one hn, stateClampDerivative_identity (by linarith) (by linarith)]
  ring

end

end NCConcave16991.GlobalHard
