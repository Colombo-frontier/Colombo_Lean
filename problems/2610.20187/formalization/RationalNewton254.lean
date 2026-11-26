import NumericalPrimitives254
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Cast.Order

namespace Paper254

/-- Computable dyadic rounding. Every output uses the same denominator. -/
def dyadicCeil (p : ℕ) (x : ℚ) : ℚ := (⌈x*(2:ℚ)^p⌉ : ℚ)/(2:ℚ)^p

def rationalNewtonStep (p : ℕ) (a x : ℚ) : ℚ := dyadicCeil p ((x+a/x)/2)

def rationalNewton (p : ℕ) (a x0 : ℚ) : ℕ → ℚ
  | 0 => x0
  | n+1 => rationalNewtonStep p a (rationalNewton p a x0 n)

theorem dyadicCeil_bounds (p : ℕ) (x : ℚ) :
    x ≤ dyadicCeil p x ∧ dyadicCeil p x ≤ x+((2:ℚ)^p)⁻¹ := by
  have hp : (0:ℚ)<2^p := by positivity
  have hlo := Int.le_ceil (x*(2:ℚ)^p)
  have hhi := Int.ceil_lt_add_one (x*(2:ℚ)^p)
  constructor
  · exact (le_div_iff₀ hp).mpr hlo
  · apply (div_le_iff₀ hp).mpr
    have he : (x+((2:ℚ)^p)⁻¹)*(2:ℚ)^p=x*(2:ℚ)^p+1 := by field_simp
    rw [he]
    exact hhi.le

theorem dyadicCeil_real_bounds (p : ℕ) (x : ℚ) :
    (x:ℝ) ≤ (dyadicCeil p x:ℝ) ∧ (dyadicCeil p x:ℝ) ≤ (x:ℝ)+((2:ℝ)^p)⁻¹ := by
  have h := dyadicCeil_bounds p x
  constructor
  · exact_mod_cast h.1
  · have hh : (dyadicCeil p x:ℝ) ≤ ((x+((2:ℚ)^p)⁻¹:ℚ):ℝ) := Rat.cast_le.mpr h.2
    push_cast at hh
    exact hh

theorem rationalNewton_step_bound (p : ℕ) (a x : ℚ) (ha : 0 < (a:ℝ))
    (hx : Real.sqrt (a:ℝ) ≤ (x:ℝ)) :
    Real.sqrt (a:ℝ) ≤ (rationalNewtonStep p a x:ℝ) ∧
      (rationalNewtonStep p a x:ℝ)-Real.sqrt (a:ℝ) ≤
        ((x:ℝ)-Real.sqrt (a:ℝ))/2+((2:ℝ)^p)⁻¹ := by
  have he := newton_sqrt_contraction (a:ℝ) (x:ℝ) ha hx
  have hr := dyadicCeil_real_bounds p ((x+a/x)/2)
  push_cast at hr
  change _ ≤ (rationalNewtonStep p a x:ℝ) ∧ (rationalNewtonStep p a x:ℝ) ≤ _ at hr
  constructor <;> linarith [he.1,he.2,hr.1,hr.2]

/-- Error is uniform in the iteration count, despite rounding every step. -/
theorem rationalNewton_error (p : ℕ) (a x0 : ℚ) (ha : 0 < (a:ℝ))
    (hx : Real.sqrt (a:ℝ) ≤ (x0:ℝ)) (n : ℕ) :
    Real.sqrt (a:ℝ) ≤ (rationalNewton p a x0 n:ℝ) ∧
      (rationalNewton p a x0 n:ℝ)-Real.sqrt (a:ℝ) ≤
        ((x0:ℝ)-Real.sqrt (a:ℝ))*(1/2:ℝ)^n+2*((2:ℝ)^p)⁻¹ := by
  induction n with
  | zero =>
    simp only [rationalNewton,pow_zero,mul_one]
    exact ⟨hx,le_add_of_nonneg_right (by positivity)⟩
  | succ n ih =>
    have hs := rationalNewton_step_bound p a (rationalNewton p a x0 n) ha ih.1
    refine ⟨hs.1,?_⟩
    change (rationalNewtonStep p a (rationalNewton p a x0 n):ℝ)-Real.sqrt (a:ℝ) ≤ _
    rw [pow_succ]
    linarith [hs.2,ih.2]

/-- Each post-update iterate has an explicitly bounded common denominator;
the recurrence does not multiply prior denominators into stored state. -/
theorem rationalNewton_encoding (p n : ℕ) (a x0 : ℚ) :
    ∃ z : ℤ,rationalNewton p a x0 (n+1)=(z:ℚ)/(2:ℚ)^p := by
  exact ⟨_,rfl⟩

end Paper254
#print axioms Paper254.rationalNewton_error
#print axioms Paper254.rationalNewton_encoding
