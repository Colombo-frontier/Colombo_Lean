import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Bandwidth/rate arithmetic

These identities verify the exponent calculation behind both halves of the
main theorem.  Write `x = d² / T` and
`pβ = (β - 1) / β`.
-/

namespace NoisyZO

noncomputable def rateExponent (β : ℝ) : ℝ := (β - 1) / β

/-- With `h = x^(1/(2β))`, the squared bias `h^(2β-2)` is exactly
`x^((β-1)/β)`. -/
theorem balanced_bias_exponent {x β : ℝ} (hx : 0 ≤ x) (hβ : 0 < β) :
    (x ^ ((1 : ℝ) / (2 * β))) ^ (2 * β - 2) =
      x ^ rateExponent β := by
  rw [← Real.rpow_mul hx]
  unfold rateExponent
  congr 1
  field_simp [ne_of_gt hβ]

/-- The variance term `x / h²` has the same exponent. -/
theorem balanced_variance_exponent {x β : ℝ} (hx : 0 < x) (hβ : 0 < β) :
    x / (x ^ ((1 : ℝ) / (2 * β))) ^ (2 : ℕ) =
      x ^ rateExponent β := by
  have hpow :
      (x ^ ((1 : ℝ) / (2 * β))) ^ (2 : ℕ) = x ^ ((1 : ℝ) / β) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hx)]
    congr 1
    norm_num only [Nat.cast_ofNat]
    field_simp [ne_of_gt hβ]
  rw [hpow]
  calc
    x / x ^ ((1 : ℝ) / β) = x ^ (1 : ℝ) / x ^ ((1 : ℝ) / β) := by
      rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) - (1 / β)) := (Real.rpow_sub hx 1 (1 / β)).symm
    _ = x ^ rateExponent β := by
      unfold rateExponent
      congr 1
      field_simp [ne_of_gt hβ]

/-- Substituting the balanced bandwidth into the complete bias--variance
tradeoff factors out the sharp rate with no hidden exponent arithmetic. -/
theorem balanced_tradeoff
    {x β B V : ℝ} (hx : 0 < x) (hβ : 0 < β) :
    B ^ 2 * (x ^ ((1 : ℝ) / (2 * β))) ^ (2 * β - 2) +
        4 * V * x / (x ^ ((1 : ℝ) / (2 * β))) ^ (2 : ℕ) =
      (B ^ 2 + 4 * V) * x ^ rateExponent β := by
  have hbias := balanced_bias_exponent (le_of_lt hx) hβ
  have hvariance := balanced_variance_exponent hx hβ
  calc
    B ^ 2 * (x ^ ((1 : ℝ) / (2 * β))) ^ (2 * β - 2) +
        4 * V * x / (x ^ ((1 : ℝ) / (2 * β))) ^ (2 : ℕ) =
        B ^ 2 * x ^ rateExponent β +
          4 * V * (x / (x ^ ((1 : ℝ) / (2 * β))) ^ (2 : ℕ)) := by
            rw [hbias]
            ring
    _ = (B ^ 2 + 4 * V) * x ^ rateExponent β := by
      rw [hvariance]
      ring

/-- Specialization of the common exponent to the explicit `β = 4` case. -/
theorem rateExponent_four : rateExponent 4 = (3 / 4 : ℝ) := by
  norm_num [rateExponent]

/-- Exact inversion of the small-error rate.  This is the arithmetic content
of the raw-query-complexity corollary. -/
theorem rate_threshold_iff
    {β d T ε : ℝ} (hβ : 1 < β) (hd : 0 < d) (hT : 0 < T) (hε : 0 < ε) :
    (d ^ 2 / T) ^ rateExponent β ≤ ε ↔
      d ^ 2 * ε ^ (-(β / (β - 1))) ≤ T := by
  have hp : 0 < rateExponent β := by
    unfold rateExponent
    positivity
  have hx : 0 ≤ d ^ 2 / T := by positivity
  have ha : 0 < ε ^ (rateExponent β)⁻¹ := Real.rpow_pos_of_pos hε _
  calc
    (d ^ 2 / T) ^ rateExponent β ≤ ε ↔
        d ^ 2 / T ≤ ε ^ (rateExponent β)⁻¹ :=
      (Real.le_rpow_inv_iff_of_pos hx hε.le hp).symm
    _ ↔ d ^ 2 / (ε ^ (rateExponent β)⁻¹) ≤ T := by
      constructor
      · intro h
        apply (div_le_iff₀ ha).2
        apply (div_le_iff₀ hT).1 at h
        nlinarith
      · intro h
        apply (div_le_iff₀ hT).2
        apply (div_le_iff₀ ha).1 at h
        nlinarith
    _ ↔ d ^ 2 * ε ^ (-(β / (β - 1))) ≤ T := by
      have hinv : (rateExponent β)⁻¹ = β / (β - 1) := by
        unfold rateExponent
        field_simp [ne_of_gt (sub_pos.mpr hβ), ne_of_gt (lt_trans zero_lt_one hβ)]
      rw [div_eq_mul_inv, hinv, ← Real.rpow_neg hε.le]

end NoisyZO
