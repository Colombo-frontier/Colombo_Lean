import MatchingBounds1005.EpsilonCalibration

/-! Explicit two-sided phase, block-width, and horizon estimates. With `ε=t³`,
the powers `t⁻⁴`, `t⁻¹`, and `t⁻⁵` are the claimed ε exponents. -/
noncomputable section
open scoped BigOperators

namespace MatchingBounds1005.EpsilonCalibration
open PathGreen

variable (a L t : ℝ) (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)

include ha hL ht in
theorem pathScale_factor : pathScale a L t = Real.sqrt (8192 * a / L) * t := by
  unfold pathScale curvature
  have heq : 8192 * a * t ^ 2 / L = (8192 * a / L) * t ^ 2 := by ring
  rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]

include ha ht in
theorem phaseCount_power_upper : (phaseCount a t : ℝ) * t ^ 4 ≤ a / (1440 * 8192) := by
  have hf := phaseCount_scaled a t ha ht
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1440 * 8192)).mpr
  nlinarith only [hf]

include ha ht in
theorem phaseCount_power_lower (hsmall : 2880 * 8192 * t ^ 4 ≤ a) :
    a / (2880 * 8192) ≤ (phaseCount a t : ℝ) * t ^ 4 := by
  let x := a / (1440 * 8192 * t ^ 4)
  have hx : 2 ≤ x := by
    apply (le_div_iff₀ (by positivity : 0 < 1440 * 8192 * t ^ 4)).mpr
    nlinarith only [hsmall]
  have hf : x < (phaseCount a t : ℝ) + 1 := Nat.lt_floor_add_one x
  have hl : x / 2 ≤ (phaseCount a t : ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_right hl (by positivity : 0 ≤ t ^ 4)
  have heq : x / 2 * t ^ 4 = a / (2880 * 8192) := by
    dsimp [x]
    field_simp
    ring
  rwa [heq] at hm

include ha hL ht in
theorem pathSize_power_bounds (hsmall : pathScale a L t ≤ 1) :
    1 / Real.sqrt (8192 * a / L) ≤ (pathSize (pathScale a L t) : ℝ) * t ∧
      (pathSize (pathScale a L t) : ℝ) * t ≤ 2 / Real.sqrt (8192 * a / L) := by
  let h := pathScale a L t
  have hh : 0 < h := pathScale_pos a L t ha hL ht
  have hk : 0 < Real.sqrt (8192 * a / L) := Real.sqrt_pos.mpr (by positivity)
  have hf := pathScale_factor a L t ha hL ht
  have hceil : h⁻¹ ≤ (pathSize h : ℝ) := Nat.le_ceil (h⁻¹)
  have hceil' : (pathSize h : ℝ) < h⁻¹ + 1 := Nat.ceil_lt_add_one (inv_pos.mpr hh).le
  have hlo : 1 ≤ h * (pathSize h : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hceil hh.le
    rwa [mul_inv_cancel₀ hh.ne'] at hm
  have hup : h * (pathSize h : ℝ) ≤ 2 := by
    have hm := mul_lt_mul_of_pos_left hceil' hh
    rw [mul_add, mul_inv_cancel₀ hh.ne', mul_one] at hm
    change h ≤ 1 at hsmall
    linarith
  change 1 ≤ pathScale a L t * (pathSize (pathScale a L t) : ℝ) at hlo
  change pathScale a L t * (pathSize (pathScale a L t) : ℝ) ≤ 2 at hup
  rw [hf] at hlo hup
  rw [hf]
  constructor
  · apply (div_le_iff₀ hk).mpr
    nlinarith only [hlo]
  · apply (le_div_iff₀ hk).mpr
    nlinarith only [hup]

include ha hL ht in
/-- Explicit positive constants in the source horizon `NM = Θ(t⁻⁵)`.
This is a proved pair of inequalities rather than an asymptotic assumption. -/
theorem horizon_power_bounds (hphase : 2880 * 8192 * t ^ 4 ≤ a)
    (hpath : pathScale a L t ≤ 1) :
    a / (2880 * 8192 * Real.sqrt (8192 * a / L)) ≤
        ((phaseCount a t * pathSize (pathScale a L t) : ℕ) : ℝ) * t ^ 5 ∧
      ((phaseCount a t * pathSize (pathScale a L t) : ℕ) : ℝ) * t ^ 5 ≤
        a / (720 * 8192 * Real.sqrt (8192 * a / L)) := by
  have hnlo := phaseCount_power_lower a t ha ht hphase
  have hnup := phaseCount_power_upper a t ha ht
  obtain ⟨hmlo, hmup⟩ := pathSize_power_bounds a L t ha hL ht hpath
  have hlo := mul_le_mul hnlo hmlo (by positivity) (by positivity)
  have hup := mul_le_mul hnup hmup (by positivity) (by positivity)
  constructor
  · convert hlo using 1 <;> push_cast <;> ring
  · convert hup using 1 <;> push_cast <;> ring

include hL ht in
/-- A simple sufficient condition for the actual quadratic budget to be at
most `8L` (and hence `b/2` when `L=b/16`). -/
theorem quadratic_coefficient_small (hsmall : t ≤ 1 / 37) :
    4 * L + 2593 * (L * t ^ 2) + 18 * Real.sqrt 2 * L * t * Real.sqrt t ≤ 8 * L := by
  have ht1 : t ≤ 1 := by linarith
  have hs : Real.sqrt t ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
  have hs2 : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht2 : 2593 * t ^ 2 ≤ 2 := by
    have hp := (sq_le_sq₀ ht.le (by norm_num : (0 : ℝ) ≤ 1 / 37)).mpr hsmall
    nlinarith only [hp]
  have hquad := mul_le_mul_of_nonneg_left ht2 hL.le
  have hc : 18 * Real.sqrt 2 * L * t * Real.sqrt t ≤ 2 * L := by
    calc
      _ ≤ 18 * 2 * L * t * 1 := by gcongr
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hsmall hL.le, hL]
  nlinarith only [hquad, hc]

end MatchingBounds1005.EpsilonCalibration
