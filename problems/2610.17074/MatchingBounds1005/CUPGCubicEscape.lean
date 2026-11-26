import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # A symmetric two-evaluation escape for a cubic polynomial

The elementary inequality here removes the unequal square-root step lengths
from the original convex-until-proven-guilty escape, without changing rates.
-/
noncomputable section

namespace MatchingBounds1005.CUPG

def cubic (a₀ a₁ a₂ a₃ t : ℝ) : ℝ := a₀ + a₁ * t + a₂ * t ^ 2 + a₃ * t ^ 3

theorem cubic_symmetric_escape (a₀ a₁ a₂ a₃ R : ℝ) (hR : 1 ≤ R) :
    min (cubic a₀ a₁ a₂ a₃ (-R)) (cubic a₀ a₁ a₂ a₃ R) ≤
      max (cubic a₀ a₁ a₂ a₃ (-1)) (cubic a₀ a₁ a₂ a₃ 1) + (a₂ - a₃) * (R ^ 2 - 1) := by
  let b := a₁ + a₃
  let c := a₃ * (R ^ 2 - 1)
  have hR0 : 0 ≤ R := by linarith
  have htriangle : c ≤ |b + c| + |b| := by
    have he : c = (b + c) - b := by ring
    calc
      c ≤ |c| := le_abs_self c
      _ ≤ |b + c| + |b| := by
        calc
          |c| = |(b + c) - b| := congrArg abs he
          _ ≤ |b + c| + |b| := abs_sub (b + c) b
  have hdom : c ≤ R * |b + c| + |b| := by
    have hm := mul_le_mul_of_nonneg_right hR (abs_nonneg (b + c))
    nlinarith only [htriangle, hm]
  have hmin : min (cubic a₀ a₁ a₂ a₃ (-R)) (cubic a₀ a₁ a₂ a₃ R) =
      a₀ + a₂ * R ^ 2 - R * |b + c| := by
    by_cases hbc : 0 ≤ b + c
    · rw [abs_of_nonneg hbc, min_eq_left]
      · dsimp [cubic, b, c]; ring
      · dsimp [cubic]
        have hp := mul_nonneg hR0 hbc
        dsimp [b, c] at hp
        nlinarith only [hp]
    · rw [abs_of_nonpos (le_of_not_ge hbc), min_eq_right]
      · dsimp [cubic, b, c]; ring
      · dsimp [cubic]
        have hp := mul_nonpos_of_nonneg_of_nonpos hR0 (le_of_not_ge hbc)
        dsimp [b, c] at hp
        nlinarith only [hp]
  have hmax : max (cubic a₀ a₁ a₂ a₃ (-1)) (cubic a₀ a₁ a₂ a₃ 1) = a₀ + a₂ + |b| := by
    by_cases hb : 0 ≤ b
    · rw [abs_of_nonneg hb, max_eq_right]
      · dsimp [cubic, b]; ring
      · dsimp [cubic, b] at *; linarith only [hb]
    · rw [abs_of_nonpos (le_of_not_ge hb), max_eq_left]
      · dsimp [cubic, b]; ring
      · dsimp [cubic, b] at *; linarith only [le_of_not_ge hb]
  rw [hmin, hmax]
  dsimp [c] at hdom
  nlinarith only [hdom]

end MatchingBounds1005.CUPG
