import NoisyZO.SphericalEstimator
import NoisyZO.WeightedAverage
import NoisyZO.RateArithmetic
import NoisyZO.QueryBudget

/-!
# Final `β = 4` upper-rate assembly

This file substitutes the explicit cubic bias and `229 d²/h²` moment
envelope into the projected-SGD telescope and verifies the balanced
`d^(3/2) n^(-3/4)` rate exactly.
-/

namespace NoisyZO

noncomputable section

/-- Balanced bandwidth for the explicit four-query estimator. -/
def betaFourBandwidth (d n : ℕ) : ℝ :=
  ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (1 / 8 : ℝ)

/-- Exact bias--variance arithmetic at the `β = 4` bandwidth. -/
theorem betaFour_balanced_tradeoff {x : ℝ} (hx : 0 < x) :
    ((x ^ (1 / 8 : ℝ)) ^ 3 / 12) ^ 2 +
        4 * (229 * x / (x ^ (1 / 8 : ℝ)) ^ 2) =
      (131905 / 144 : ℝ) * x ^ (3 / 4 : ℝ) := by
  have h := balanced_tradeoff
    (x := x) (β := 4) (B := (1 / 12 : ℝ)) (V := 229) hx (by norm_num)
  rw [rateExponent_four] at h
  convert h using 1 <;> norm_num <;> ring

/-- Once the expected projected steps have the concrete estimator's bias and
moment constants, the complete weighted-SGD output obeys the sharp balanced
rate.  The premise is exactly the recurrence supplied by
`projected_biased_gradient_step_expectation`. -/
theorem NormalizedObjective.betaFour_sgd_balanced_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (n : ℕ) (hn : 0 < n) (hd : 0 < d)
    (xseq : ℕ → Point d) (R : ℕ → ℝ)
    (hR : ∀ t, 0 ≤ R t)
    (hstep : ∀ k < n,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) *
            (F.f (xseq (k + 1)) - F.f F.minimizer) +
          2 * (4 / (k + 2 : ℝ)) *
            ((betaFourBandwidth d n) ^ 3 / 12) ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 *
            (229 * d ^ 2 / (betaFourBandwidth d n) ^ 2)) :
    F.f (sgdWeightedAverage n xseq) - F.f F.minimizer ≤
      (131905 / 144 : ℝ) *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by
  let ratio : ℝ := (d : ℝ) ^ 2 / (n + 1 : ℝ)
  have hratio : 0 < ratio := by
    dsimp [ratio]
    positivity
  have hmoment : 0 ≤ 229 * (d : ℝ) ^ 2 / (betaFourBandwidth d n) ^ 2 := by
    positivity
  have hmain := F.sgdWeightedAverage_final_bound n hn xseq R
    ((betaFourBandwidth d n) ^ 3 / 12)
    (229 * (d : ℝ) ^ 2 / (betaFourBandwidth d n) ^ 2)
    hmoment hR hstep
  calc
    F.f (sgdWeightedAverage n xseq) - F.f F.minimizer ≤
        ((betaFourBandwidth d n) ^ 3 / 12) ^ 2 +
          4 * (229 * (d : ℝ) ^ 2 / (betaFourBandwidth d n) ^ 2) /
            (n + 1 : ℝ) := hmain
    _ = ((ratio ^ (1 / 8 : ℝ)) ^ 3 / 12) ^ 2 +
        4 * (229 * ratio / (ratio ^ (1 / 8 : ℝ)) ^ 2) := by
      dsimp [ratio, betaFourBandwidth]
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn1]
    _ = (131905 / 144 : ℝ) * ratio ^ (3 / 4 : ℝ) :=
      betaFour_balanced_tradeoff hratio
    _ = (131905 / 144 : ℝ) *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by rfl

/-- Four raw oracle calls per iteration convert the explicit `β = 4`
iteration rate to the corresponding high-budget raw-call rate. -/
theorem NormalizedObjective.betaFour_sgd_raw_budget_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (T : ℕ) (hT : 8 ≤ T) (hd : 0 < d)
    (xseq : ℕ → Point d) (R : ℕ → ℝ)
    (hR : ∀ t, 0 ≤ R t)
    (hstep : ∀ k < T / 4,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) *
            (F.f (xseq (k + 1)) - F.f F.minimizer) +
          2 * (4 / (k + 2 : ℝ)) *
            ((betaFourBandwidth d (T / 4)) ^ 3 / 12) ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 *
            (229 * d ^ 2 / (betaFourBandwidth d (T / 4)) ^ 2)) :
    F.f (sgdWeightedAverage (T / 4) xseq) - F.f F.minimizer ≤
      (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
        ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) := by
  let n : ℕ := T / 4
  have hn : 0 < n := by
    dsimp only [n]
    omega
  have hmain := F.betaFour_sgd_balanced_rate n hn hd xseq R hR (by
    simpa only [n] using hstep)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1R : 0 < (n + 1 : ℝ) := by positivity
  have hratioSucc :
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ (d : ℝ) ^ 2 / n := by
    apply (div_le_div_iff₀ hn1R hnR).2
    nlinarith [sq_nonneg (d : ℝ)]
  have hscheduled : (d : ℝ) ^ 2 / n ≤ 8 * (d : ℝ) ^ 2 / T := by
    have hraw := dimension_ratio_scheduled_le (d := d) (T := T) (q := 4)
      (by norm_num) hT
    norm_num at hraw
    simpa only [n] using hraw
  have hratio :
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ 8 * ((d : ℝ) ^ 2 / T) := by
    calc
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ (d : ℝ) ^ 2 / n := hratioSucc
      _ ≤ 8 * (d : ℝ) ^ 2 / T := hscheduled
      _ = 8 * ((d : ℝ) ^ 2 / T) := by ring
  have hpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ (d : ℝ) ^ 2 / (n + 1 : ℝ)) hratio
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  calc
    F.f (sgdWeightedAverage (T / 4) xseq) - F.f F.minimizer ≤
        (131905 / 144 : ℝ) *
          ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by
      simpa only [n] using hmain
    _ ≤ (131905 / 144 : ℝ) *
        (8 * ((d : ℝ) ^ 2 / T)) ^ (3 / 4 : ℝ) := by
      gcongr
    _ = (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
        ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring

/-- Use weighted four-query SGD above the dimension-dependent threshold and
the zero-query output below it. -/
def betaFourBudgetOutput {d : ℕ}
    (T : ℕ) (xseq : ℕ → Point d) : Point d :=
  if 8 * d ^ 2 ≤ T then sgdWeightedAverage (T / 4) xseq else 0

/-- Complete saturated raw-budget upper rate at `β = 4`, including the
small-budget branch. -/
theorem NormalizedObjective.betaFour_sgd_saturated_raw_budget_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (T : ℕ) (hT : 0 < T) (hd : 0 < d)
    (xseq : ℕ → Point d) (R : ℕ → ℝ)
    (hR : ∀ t, 0 ≤ R t)
    (hstep : ∀ k < T / 4,
      R (k + 2) ≤
        (1 - (4 / (k + 2 : ℝ)) / 2) * R (k + 1) -
          2 * (4 / (k + 2 : ℝ)) *
            (F.f (xseq (k + 1)) - F.f F.minimizer) +
          2 * (4 / (k + 2 : ℝ)) *
            ((betaFourBandwidth d (T / 4)) ^ 3 / 12) ^ 2 +
          (4 / (k + 2 : ℝ)) ^ 2 *
            (229 * d ^ 2 / (betaFourBandwidth d (T / 4)) ^ 2)) :
    F.f (betaFourBudgetOutput T xseq) - F.f F.minimizer ≤
      (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
        min 1 (((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ)) := by
  by_cases hlarge : 8 * d ^ 2 ≤ T
  · have hT8 : 8 ≤ T := by
      have hd1 : 1 ≤ d := hd
      nlinarith [Nat.one_le_pow 2 d]
    have hmain := F.betaFour_sgd_raw_budget_rate T hT8 hd xseq R hR hstep
    have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
    have hlargeR : (8 : ℝ) * (d : ℝ) ^ 2 ≤ T := by exact_mod_cast hlarge
    have hratioOne : (d : ℝ) ^ 2 / T ≤ 1 := by
      rw [div_le_one hTR]
      nlinarith [sq_nonneg (d : ℝ)]
    have hpowOne :
        ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by positivity : 0 ≤ (d : ℝ) ^ 2 / T)
          hratioOne (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rw [betaFourBudgetOutput, if_pos hlarge, min_eq_right hpowOne]
    exact hmain
  · have hsmall : T < 8 * d ^ 2 := Nat.lt_of_not_ge hlarge
    have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
    have hsmallR : (T : ℝ) < 8 * (d : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hratioLower : (1 / 8 : ℝ) < (d : ℝ) ^ 2 / T := by
      rw [lt_div_iff₀ hTR]
      nlinarith
    have hpowLower :
        (1 / 8 : ℝ) ^ (3 / 4 : ℝ) ≤
          ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hratioLower.le (by norm_num)
    have hpowFloor :
        (1 / 8 : ℝ) ^ (3 / 4 : ℝ) ≤
          min 1 (((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ)) := by
      apply le_min
      · simpa only [Real.one_rpow] using
          Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8)
            (by norm_num : (1 / 8 : ℝ) ≤ 1)
            (by norm_num : (0 : ℝ) ≤ 3 / 4)
      · exact hpowLower
    have hcancel :
        (8 : ℝ) ^ (3 / 4 : ℝ) *
          (1 / 8 : ℝ) ^ (3 / 4 : ℝ) = 1 := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    rw [betaFourBudgetOutput, if_neg hlarge]
    calc
      F.f 0 - F.f F.minimizer ≤ 9 := F.zero_gap_le_nine
      _ ≤ (131905 / 144 : ℝ) := by norm_num
      _ = (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
          (1 / 8 : ℝ) ^ (3 / 4 : ℝ) := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
          min 1 (((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ)) := by
        gcongr

end

end NoisyZO
