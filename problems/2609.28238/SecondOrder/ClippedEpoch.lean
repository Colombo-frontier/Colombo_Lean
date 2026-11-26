import SecondOrder.Rates
import Mathlib.Data.Nat.Log

namespace SecondOrder
noncomputable section

/-- Round upward, then clip to the nonempty integer interval [1,Q]. -/
def clippedCeil (Q : ℕ) (x : ℝ) : ℕ := min Q (max 1 ⌈x⌉₊)

theorem clippedCeil_pos {Q : ℕ} (hQ : 0 < Q) (x : ℝ) : 0 < clippedCeil Q x := by
  unfold clippedCeil
  omega

theorem clippedCeil_le (Q : ℕ) (x : ℝ) : clippedCeil Q x ≤ Q := min_le_left _ _

theorem clippedCeil_eq_one {Q : ℕ} (hQ : 0 < Q) {x : ℝ} (hx : x ≤ 1) : clippedCeil Q x = 1 := by
  have hc : ⌈x⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using hx)
  unfold clippedCeil
  omega

theorem clippedCeil_eq_cap {Q : ℕ} {x : ℝ} (hx : (Q : ℝ) ≤ x) : clippedCeil Q x = Q := by
  have hc : Q ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
  unfold clippedCeil
  omega

theorem clippedCeil_eq_ceil {Q : ℕ} {x : ℝ} (hx : 1 < x) (hQ : x ≤ Q) :
    clippedCeil Q x = ⌈x⌉₊ := by
  have hlo : (1 : ℝ) < (⌈x⌉₊ : ℝ) := hx.trans_le (Nat.le_ceil x)
  have hn : 1 < ⌈x⌉₊ := by exact_mod_cast hlo
  have hc : ⌈x⌉₊ ≤ Q := Nat.ceil_le.mpr hQ
  unfold clippedCeil
  omega

/-- Clipping and rounding cost only the two endpoint contributions and
a constant multiple of the balanced value. No asymptotic notation is used. -/
theorem clippedCeil_balance {A B x : ℝ} {Q : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 < x) (hQ : 0 < Q) (he : A = B*x^2) :
    A/(clippedCeil Q x : ℝ)+B*(clippedCeil Q x : ℝ) ≤ 4*B*x+2*B+2*A/(Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  by_cases hlo : x ≤ 1
  · rw [clippedCeil_eq_one hQ hlo]
    have hsq : x^2 ≤ 1 := by nlinarith
    have hAB : A ≤ B := by nlinarith [mul_le_mul_of_nonneg_left hsq hB]
    have hb := clipped_balance_left hAB
    norm_num only [Nat.cast_one] at ⊢
    have hpos : 0 ≤ 4*B*x := by positivity
    have hdiv : 0 ≤ 2*A/(Q : ℝ) := by positivity
    linarith
  · by_cases hhi : (Q : ℝ) ≤ x
    · rw [clippedCeil_eq_cap hhi]
      have hsq : (Q : ℝ)^2 ≤ x^2 := pow_le_pow_left₀ hQr.le hhi 2
      have hBQ : B*(Q : ℝ)^2 ≤ A := by rw [he]; exact mul_le_mul_of_nonneg_left hsq hB
      have hb := clipped_balance_right hQr hBQ
      have hpos : 0 ≤ 4*B*x := by positivity
      linarith
    · rw [clippedCeil_eq_ceil (lt_of_not_ge hlo) (le_of_lt (lt_of_not_ge hhi))]
      have hround : (⌈x⌉₊ : ℝ) ≤ 2*x := by
        have hc := Nat.ceil_lt_add_one hx.le
        linarith
      have hb := balance_rounding hA hB hx (Nat.le_ceil x) hround
      rw [balance_exact hx he] at hb
      have hdiv : 0 ≤ 2*A/(Q : ℝ) := by positivity
      nlinarith

end
end SecondOrder
