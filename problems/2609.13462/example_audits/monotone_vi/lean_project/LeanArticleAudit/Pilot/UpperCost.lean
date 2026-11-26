import LeanArticleAudit.Pilot.UpperInterfaces

/-!
# Scalar query-cost aggregation

These lemmas keep the finite schedule accounting separate from the executable
syntax.  They do not assume an oracle algorithm: callers must supply the
proved per-call cap and the proved numbers of public radius/stage trials.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The article's strong logarithmic factor is at least one on its public
positive parameter domain. -/
theorem strongLog_one_le (data : VIPublicData E) (mu delta : ℝ)
    (hmu : 0 < mu) (hdelta : 0 < delta) :
    1 ≤ strongLog data mu delta := by
  unfold strongLog
  have h1 : 1 ≤ 2 + data.Lp * data.D ^ (data.p - 1) / mu +
      data.Lp * data.D ^ data.p / delta + mu * data.D / delta := by
    have hD : 0 ≤ data.D := data.D_pos.le
    have hLp : 0 ≤ data.Lp := data.Lp_pos.le
    have hA : 0 ≤ data.Lp * data.D ^ (data.p - 1) / mu := by positivity
    have hB : 0 ≤ data.Lp * data.D ^ data.p / delta := by positivity
    have hC : 0 ≤ mu * data.D / delta := by positivity
    linarith
  linarith [Real.log_nonneg h1]

/-- The residual logarithmic factor is likewise at least one. -/
theorem residualLog_one_le (data : VIPublicData E) (R epsilon : ℝ)
    (hR : 0 < R) (hepsilon : 0 < epsilon) :
    1 ≤ residualLog data R epsilon := by
  unfold residualLog residualCondition
  have h1 : 1 ≤ 2 + data.D / R + data.Lp * R ^ data.p / epsilon := by
    have hD : 0 ≤ data.D := data.D_pos.le
    have hLp : 0 ≤ data.Lp := data.Lp_pos.le
    have hA : 0 ≤ data.D / R := by positivity
    have hB : 0 ≤ data.Lp * R ^ data.p / epsilon := by positivity
    linarith
  linarith [Real.log_nonneg h1]

/-- A natural ceiling of a base-two logarithm is a certified power-of-two
upper scale. -/
theorem positive_le_two_pow_natCeil_logb (c : ℝ) (hc : 0 < c) :
    c ≤ (2 : ℝ) ^ (⌈Real.logb 2 c⌉₊ : ℕ) := by
  have hlog : Real.logb 2 c ≤ (⌈Real.logb 2 c⌉₊ : ℝ) := Nat.le_ceil _
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hc).mp hlog
  simpa [Real.rpow_natCast] using h

/-- Uniform real upper bound for a natural ceiling, including the negative
input branch where `Nat.ceil` is zero. -/
theorem natCeil_cast_le_max_add_one (x : ℝ) :
    (⌈x⌉₊ : ℝ) ≤ max 0 x + 1 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx]
    exact (Nat.ceil_lt_add_one hx).le
  · have hceil : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr (le_of_not_ge hx)
    rw [hceil, Nat.cast_zero, max_eq_left (le_of_not_ge hx)]
    norm_num

/-- Two-sided real bounds for the ubiquitous public schedule
`max 2 ⌈x⌉₊`. -/
theorem max_two_natCeil_bounds (x : ℝ) (hx : 0 ≤ x) :
    x ≤ (max 2 ⌈x⌉₊ : ℕ) ∧
      ((max 2 ⌈x⌉₊ : ℕ) : ℝ) ≤ x + 2 := by
  constructor
  · exact (Nat.le_ceil x).trans (by
      exact_mod_cast (Nat.le_max_right 2 ⌈x⌉₊))
  · rw [Nat.cast_max]
    apply max_le
    · norm_num
      linarith
    · exact (Nat.ceil_lt_add_one hx).le.trans (by linarith)

/-- Two nested public schedules cost at most two additional powers of the
strong logarithm.  This is the arithmetic core of `lem:restart`. -/
theorem restart_two_schedule_aggregate
    {C q LS : ℝ} {alpha : ℝ} {b : ℕ} {guesses stages : ℕ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hLS : 1 ≤ LS)
    (hguesses : (guesses : ℝ) ≤ LS)
    (hstages : (stages : ℝ) ≤ LS) :
    (guesses : ℝ) * (stages : ℝ) *
        (C * (1 + q ^ alpha) * LS ^ b) ≤
      C * (1 + q ^ alpha) * LS ^ (b + 2) := by
  have hqpow : 0 ≤ q ^ alpha := Real.rpow_nonneg hq alpha
  have hLS0 : 0 ≤ LS := le_trans (by norm_num) hLS
  have hgs : (guesses : ℝ) * (stages : ℝ) ≤ LS ^ 2 := by
    calc
      (guesses : ℝ) * (stages : ℝ) ≤ LS * LS := by
        exact mul_le_mul hguesses hstages (by positivity) hLS0
      _ = LS ^ 2 := by ring
  calc
    (guesses : ℝ) * (stages : ℝ) *
        (C * (1 + q ^ alpha) * LS ^ b)
      ≤ LS ^ 2 * (C * (1 + q ^ alpha) * LS ^ b) := by
        gcongr
    _ = C * (1 + q ^ alpha) * LS ^ (b + 2) := by
      rw [pow_add]
      ring

/-- Summing finitely many nonnegative per-call caps by a common public
majorant. -/
theorem finite_calls_le_card_mul
    {n : ℕ} {cost : Fin n → ℝ} {M : ℝ}
    (hcost : ∀ i, 0 ≤ cost i ∧ cost i ≤ M) :
    (∑ i, cost i) ≤ (n : ℝ) * M := by
  calc
    (∑ i, cost i) ≤ ∑ _i : Fin n, M :=
      Finset.sum_le_sum fun i _ ↦ (hcost i).2
    _ = (n : ℝ) * M := by simp

/-- Ceiling overhead of `n` locally capped children is at most one query per
child in addition to their real-valued interface bounds. -/
theorem sum_natCeil_le
    {n : ℕ} {cost : Fin n → ℝ} (hcost : ∀ i, 0 ≤ cost i) :
    ((∑ i, ⌈cost i⌉₊ : ℕ) : ℝ) ≤ (∑ i, cost i) + n := by
  push_cast
  have hpoint : ∀ i : Fin n, (⌈cost i⌉₊ : ℝ) ≤ cost i + 1 := by
    intro i
    exact le_of_lt (Nat.ceil_lt_add_one (hcost i))
  calc
    (∑ i, (⌈cost i⌉₊ : ℝ)) ≤ ∑ i, (cost i + 1) :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = (∑ i, cost i) + n := by
      rw [Finset.sum_add_distrib]
      simp

end

end LeanArticleAudit.Pilot
