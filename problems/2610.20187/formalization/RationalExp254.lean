import RationalNewton254
import Mathlib.Analysis.Complex.Exponential

open scoped BigOperators
namespace Paper254

/-- Exact rational Taylor polynomial, with a precision-driven term count. -/
def rationalExp (x : ℚ) (p : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (p+3),x^k/(k.factorial : ℚ)

theorem rationalExp_error (x : ℚ) (p : ℕ) (hx : |(x:ℝ)| ≤ 1/2) :
    |Real.exp (x:ℝ)-(rationalExp x p:ℝ)| ≤ ((2:ℝ)^p)⁻¹/4 := by
  have hh := Real.exp_bound (show |(x:ℝ)| ≤ 1 by linarith) (by omega : 0 < p+3)
  have hn : (1:ℝ) ≤ p+3 := by linarith [Nat.cast_nonneg p (α := ℝ)]
  have hf : (1:ℝ) ≤ (p+3).factorial := by exact_mod_cast Nat.factorial_pos (p+3)
  have hd : (0:ℝ) < ((p+3).factorial : ℝ)*(p+3) := by positivity
  have hr : ((p+3).succ : ℝ)/((p+3).factorial*(p+3) : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hd).mpr
    push_cast
    nlinarith
  have hp : |(x:ℝ)|^(p+3) ≤ (1/2:ℝ)^(p+3) := pow_le_pow_left₀ (abs_nonneg _) hx _
  have hm := mul_le_mul hp hr (by positivity) (by positivity : 0 ≤ (1/2:ℝ)^(p+3))
  have he : (1/2:ℝ)^(p+3)*2=((2:ℝ)^p)⁻¹/4 := by
    rw [pow_add]
    simp [one_div_pow]
    ring
  rw [he] at hm
  have hc : (rationalExp x p:ℝ)=∑ k ∈ Finset.range (p+3),(x:ℝ)^k/(k.factorial : ℝ) := by
    simp [rationalExp]
  rw [hc]
  apply hh.trans
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hm

end Paper254
#print axioms Paper254.rationalExp_error
