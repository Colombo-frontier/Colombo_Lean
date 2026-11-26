import VIReference.Pilot.DeterministicLower

/-!
# The finite-budget deterministic lower bound as a complexity statement

This module isolates the inversion behind the “In particular” sentence of
`thm:det`.  The ambient dimension remains explicit, as required by the
high-dimensional worst-case model.
-/

open Set
open scoped RealInnerProductSpace

namespace VIReference.Pilot

universe u

/-- `2/(3p-1)`, the deterministic lower-bound exponent. -/
noncomputable def deterministicRateExponent (p : ℕ) : ℝ :=
  2 / (3 * (p : ℝ) - 1)

/-- The reciprocal exponent `(3p-1)/2`. -/
noncomputable def deterministicRatePower (p : ℕ) : ℝ :=
  (3 * (p : ℝ) - 1) / 2

/-- The dimensionless condition number `L_p D^p / epsilon`. -/
noncomputable def deterministicConditionNumber
    (p : ℕ) (Lp D epsilon : ℝ) : ℝ :=
  Lp * D ^ p / epsilon

/-- The exact `p`-dependent denominator left after writing `D=2R`. -/
noncomputable def deterministicResidualDenominator
    (p : ℕ) (profile : GateProfile) : ℝ :=
  8 * gateBp p profile * 16 ^ (p - 1) * 2 ^ p

/-- A deliberately conservative positive Omega constant.  Its smallness
absorbs `m=N+1 <= 2N` for every positive query budget. -/
noncomputable def deterministicOmegaConstant
    (p : ℕ) (profile : GateProfile) : ℝ :=
  ((1 / deterministicResidualDenominator p profile) ^
      deterministicRateExponent p) / 2

theorem deterministicResidualDenominator_pos (p : ℕ) (profile : GateProfile) :
    0 < deterministicResidualDenominator p profile := by
  dsimp [deterministicResidualDenominator]
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) (gateBp_pos p profile)) (pow_pos (by norm_num) _))
    (pow_pos (by norm_num) _)

theorem deterministicOmegaConstant_pos (p : ℕ) (hp : 2 ≤ p)
    (profile : GateProfile) :
    0 < deterministicOmegaConstant p profile := by
  rw [deterministicOmegaConstant]
  exact div_pos (Real.rpow_pos_of_pos
    (div_pos zero_lt_one (deterministicResidualDenominator_pos p profile)) _) (by norm_num)

theorem hiddenM_power_sqrt_eq_rpow (p N : ℕ) (hp : 1 ≤ p) :
    (hiddenM N : ℝ) ^ p * Real.sqrt (hiddenM N : ℝ) ^ (p - 1) =
      (hiddenM N : ℝ) ^ deterministicRatePower p := by
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast]
  have hsqrtPow : ((hiddenM N : ℝ) ^ (1 / 2 : ℝ)) ^ (p - 1) =
      (hiddenM N : ℝ) ^ ((1 / 2 : ℝ) * (p - 1 : ℕ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
  rw [hsqrtPow]
  rw [← Real.rpow_add hm0]
  congr 1
  dsimp [deterministicRatePower]
  rw [Nat.cast_sub hp]
  push_cast
  ring

theorem hiddenM_power_sqrt_sq (p N : ℕ) (hp : 1 ≤ p) :
    ((hiddenM N : ℝ) ^ p * Real.sqrt (hiddenM N : ℝ) ^ (p - 1)) ^ 2 =
      (hiddenM N : ℝ) ^ (3 * p - 1) := by
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  rw [hiddenM_power_sqrt_eq_rpow p N hp]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hm0.le]
  have hexp : deterministicRatePower p * (2 : ℝ) = (3 * p - 1 : ℕ) := by
    dsimp [deterministicRatePower]
    rw [Nat.cast_sub (by omega : 1 ≤ 3 * p)]
    push_cast
    ring
  norm_num at hexp ⊢
  rw [hexp, Real.rpow_natCast]

theorem hiddenResidualClosedForm_eq_D_condition
    (p : ℕ) (profile : GateProfile) (Lp R epsilon : ℝ) :
    hiddenResidualClosedForm p profile Lp R N =
      (Lp * (2 * R) ^ p) /
        (deterministicResidualDenominator p profile *
          ((hiddenM N : ℝ) ^ p * Real.sqrt (hiddenM N : ℝ) ^ (p - 1))) := by
  have hBp : gateBp p profile ≠ 0 := (gateBp_pos p profile).ne'
  have hm : (hiddenM N : ℝ) ≠ 0 := by exact_mod_cast (hiddenM_pos N).ne'
  have hs : Real.sqrt (hiddenM N : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast hiddenM_pos N)
  rw [hiddenResidualClosedForm, deterministicResidualDenominator, mul_pow]
  field_simp [hBp, hm, hs]

/-- A purely algebraic finite-budget inversion.  It displays the exponent
`3p-1` without relying on asymptotic notation. -/
theorem finite_threshold_of_squared_complexity_gate
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp R epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hepsilon : 0 < epsilon) (N : ℕ)
    (hgate : deterministicResidualDenominator p profile ^ 2 *
      (hiddenM N : ℝ) ^ (3 * p - 1) <
        deterministicConditionNumber p Lp (2 * R) epsilon ^ 2) :
    epsilon < hiddenResidualClosedForm p profile Lp R N := by
  let C := deterministicResidualDenominator p profile
  let A := (hiddenM N : ℝ) ^ p * Real.sqrt (hiddenM N : ℝ) ^ (p - 1)
  let Q := deterministicConditionNumber p Lp (2 * R) epsilon
  have hC : 0 < C := deterministicResidualDenominator_pos p profile
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hQ : 0 < Q := by
    dsimp [Q, deterministicConditionNumber]
    positivity
  have hsq : (C * A) ^ 2 < Q ^ 2 := by
    rw [mul_pow, hiddenM_power_sqrt_sq p N (by omega)]
    simpa [C, A, Q, mul_assoc] using hgate
  have hCA : C * A < Q := (sq_lt_sq₀ (mul_nonneg hC.le hA.le) hQ.le).1 hsq
  have hnum : 0 < Lp * (2 * R) ^ p := by positivity
  have hineq : epsilon < (Lp * (2 * R) ^ p) / (C * A) := by
    dsimp [Q, deterministicConditionNumber] at hCA
    apply (lt_div_iff₀ (mul_pos hC hA)).2
    have hmul := (lt_div_iff₀ hepsilon).1 hCA
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [hiddenResidualClosedForm_eq_D_condition p profile Lp R epsilon]
  exact hineq

theorem deterministicRateExponent_pos (p : ℕ) (hp : 2 ≤ p) :
    0 < deterministicRateExponent p := by
  rw [deterministicRateExponent]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact div_pos (by norm_num) (by nlinarith)

theorem squared_gate_of_m_lt_rpow_scale
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp R epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hepsilon : 0 < epsilon) (N : ℕ)
    (hm : (hiddenM N : ℝ) <
      (deterministicConditionNumber p Lp (2 * R) epsilon /
        deterministicResidualDenominator p profile) ^
          deterministicRateExponent p) :
    deterministicResidualDenominator p profile ^ 2 *
      (hiddenM N : ℝ) ^ (3 * p - 1) <
        deterministicConditionNumber p Lp (2 * R) epsilon ^ 2 := by
  let C := deterministicResidualDenominator p profile
  let Q := deterministicConditionNumber p Lp (2 * R) epsilon
  let k : ℕ := 3 * p - 1
  have hC : 0 < C := deterministicResidualDenominator_pos p profile
  have hQ : 0 < Q := by
    dsimp [Q, deterministicConditionNumber]
    positivity
  have hm0 : (0 : ℝ) ≤ hiddenM N := by positivity
  have hk : 0 < (k : ℝ) := by
    exact_mod_cast (show 0 < k by dsimp [k]; omega)
  have hr := Real.rpow_lt_rpow hm0 hm hk
  have halpha : deterministicRateExponent p * (k : ℝ) = 2 := by
    dsimp [deterministicRateExponent, k]
    rw [Nat.cast_sub (by omega : 1 ≤ 3 * p)]
    push_cast
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hden : 3 * (p : ℝ) - 1 ≠ 0 := by nlinarith
    field_simp [hden]
  have hpow : (hiddenM N : ℝ) ^ k < (Q / C) ^ 2 := by
    rw [← Real.rpow_natCast]
    calc
      (hiddenM N : ℝ) ^ (k : ℝ) <
          ((Q / C) ^ deterministicRateExponent p) ^ (k : ℝ) := hr
      _ = (Q / C) ^
          (deterministicRateExponent p * (k : ℝ)) := by
            rw [Real.rpow_mul (div_nonneg hQ.le hC.le)]
      _ = (Q / C) ^ 2 := by rw [halpha, Real.rpow_two]
  dsimp [C, Q, k] at hpow ⊢
  have hCne := (deterministicResidualDenominator_pos p profile).ne'
  have hC2 : 0 < deterministicResidualDenominator p profile ^ 2 := sq_pos_of_pos
    (deterministicResidualDenominator_pos p profile)
  have hmul := mul_lt_mul_of_pos_left hpow hC2
  calc
    deterministicResidualDenominator p profile ^ 2 *
        (hiddenM N : ℝ) ^ (3 * p - 1) <
      deterministicResidualDenominator p profile ^ 2 *
        (deterministicConditionNumber p Lp (2 * R) epsilon /
          deterministicResidualDenominator p profile) ^ 2 := hmul
    _ = deterministicConditionNumber p Lp (2 * R) epsilon ^ 2 := by
      field_simp

/-- The explicit Omega budget condition implies the exact squared gate used
by the finite lower bound. -/
theorem squared_gate_of_budget_lt_omega_scale
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp R epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hepsilon : 0 < epsilon) (N : ℕ) (hN : 1 ≤ N)
    (hbudgetScale : (N : ℝ) < deterministicOmegaConstant p profile *
      deterministicConditionNumber p Lp (2 * R) epsilon ^
        deterministicRateExponent p) :
    deterministicResidualDenominator p profile ^ 2 *
      (hiddenM N : ℝ) ^ (3 * p - 1) <
        deterministicConditionNumber p Lp (2 * R) epsilon ^ 2 := by
  let C := deterministicResidualDenominator p profile
  let Q := deterministicConditionNumber p Lp (2 * R) epsilon
  let alpha := deterministicRateExponent p
  have hC : 0 < C := deterministicResidualDenominator_pos p profile
  have hQ : 0 < Q := by
    dsimp [Q, deterministicConditionNumber]
    positivity
  have hQa : 0 < Q ^ alpha := Real.rpow_pos_of_pos hQ _
  have hNm : (hiddenM N : ℝ) ≤ 2 * (N : ℝ) := by
    simp [hiddenM]
    norm_cast
    omega
  have htwo : 2 * (N : ℝ) <
      2 * (deterministicOmegaConstant p profile * Q ^ alpha) := by
    apply mul_lt_mul_of_pos_left
    simpa [Q, alpha] using hbudgetScale
    norm_num
  have hscale : 2 * (deterministicOmegaConstant p profile * Q ^ alpha) =
      (Q / C) ^ alpha := by
    rw [deterministicOmegaConstant]
    have hcinv : 0 ≤ 1 / C := (div_pos zero_lt_one hC).le
    have hq0 : 0 ≤ Q := hQ.le
    rw [show (2 : ℝ) * (((1 / C) ^ alpha / 2) * Q ^ alpha) =
      (1 / C) ^ alpha * Q ^ alpha by ring]
    rw [← Real.mul_rpow hcinv hq0]
    congr 1
    field_simp
  apply squared_gate_of_m_lt_rpow_scale p hp profile Lp R epsilon
    hLp hR hepsilon N
  calc
    (hiddenM N : ℝ) ≤ 2 * (N : ℝ) := hNm
    _ < 2 * (deterministicOmegaConstant p profile * Q ^ alpha) := htwo
    _ = (Q / C) ^ alpha := hscale

/-- Exact finite-`N` epsilon gate.  This is the operational consequence of
`deterministicLowerClaim_proof` before asymptotic inversion. -/
theorem deterministic_hard_instance_of_finite_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp R epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (N : ℕ) (hN : 1 ≤ N) (budget : ℕ) (hbudget : budget ≤ N)
    (hdim : 2 * N + 2 ≤ Module.finrank ℝ E)
    (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
      (ExactJet E p) budget)
    (hthreshold : epsilon < hiddenResidualClosedForm p profile Lp R N) :
    ∃ v : Fin (N + 1) → E,
      Orthonormal ℝ v ∧
      IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
        (hiddenOperator p profile Lp R N v) ∧
      epsilon < tangentResidual
        (ballVIData (E := E) p hp Lp hLp R hR)
        (hiddenOperator p profile Lp R N v)
        (policy.run (exactJet p
          (hiddenOperator p profile Lp R N v))).1 := by
  obtain ⟨v, hv, hadm, hlower⟩ :=
    deterministicLowerClaim_proof E p hp profile Lp R hLp hR N hN
      budget hbudget hdim policy
  exact ⟨v, hv, hadm, hthreshold.trans_le hlower⟩

/-- Operational high-dimensional meaning of the `Omega_p` conclusion in
`thm:det`.  `DeterministicPolicy` has a hard cap `N` but may stop at any
earlier leaf, so this quantifies algorithms using *at most* `N` queries.

The witness constant depends only on `p` and the fixed gate profile.  The
public diameter is displayed as `D=2R`, and the dimensionless scale and
exponent occur literally in the budget premise. -/
def DeterministicHighDimensionalComplexityLowerClaim : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile),
    ∃ c_p : ℝ, c_p = deterministicOmegaConstant p profile ∧ 0 < c_p ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [Nontrivial E]
        (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
        (hD : D = 2 * R) (hepsilon : 0 < epsilon)
        (N : ℕ) (hN : 1 ≤ N)
        (hdim : 2 * N + 2 ≤ Module.finrank ℝ E)
        (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
          (ExactJet E p) N),
        (N : ℝ) < c_p *
          deterministicConditionNumber p Lp D epsilon ^
            deterministicRateExponent p →
        ∃ v : Fin (N + 1) → E,
          Orthonormal ℝ v ∧
          IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N v) ∧
          epsilon < tangentResidual
            (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N v)
            (policy.run (exactJet p
              (hiddenOperator p profile Lp R N v))).1

/-- Kernel-checked deterministic complexity lower bound with explicit
constant and exponent `2/(3p-1)`. -/
theorem deterministicHighDimensionalComplexityLowerClaim_proof :
    DeterministicHighDimensionalComplexityLowerClaim := by
  intro p hp profile
  refine ⟨deterministicOmegaConstant p profile, rfl,
    deterministicOmegaConstant_pos p hp profile, ?_⟩
  intro E _ _ _ _ Lp R D epsilon hLp hR hD hepsilon N hN hdim policy hbudget
  subst D
  have hsq := squared_gate_of_budget_lt_omega_scale p hp profile
    Lp R epsilon hLp hR hepsilon N hN hbudget
  have hthreshold := finite_threshold_of_squared_complexity_gate p hp profile
    Lp R epsilon hLp hR hepsilon N hsq
  exact deterministic_hard_instance_of_finite_threshold p hp profile
    Lp R epsilon hLp hR hepsilon N hN N le_rfl hdim policy hthreshold

/-- Short audit-facing name for the operational `Omega_p` clause. -/
def DeterministicOmegaLowerClaim : Prop :=
  DeterministicHighDimensionalComplexityLowerClaim.{u}

theorem deterministicOmegaLowerClaim_proof : DeterministicOmegaLowerClaim :=
  deterministicHighDimensionalComplexityLowerClaim_proof

/-- Full audited content of `thm:det`: the exact finite-budget hard instance
and its explicit high-dimensional worst-case complexity consequence. -/
def DeterministicTheoremClaim : Prop :=
  DeterministicLowerClaim.{u} ∧ DeterministicOmegaLowerClaim.{u}

theorem deterministicTheoremClaim_proof : DeterministicTheoremClaim :=
  ⟨deterministicLowerClaim_proof, deterministicOmegaLowerClaim_proof⟩

end VIReference.Pilot
