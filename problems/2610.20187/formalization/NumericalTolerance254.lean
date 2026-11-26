import RationalWorkingBounds254
import Mathlib.Algebra.Order.Floor.Semiring

namespace Paper254

noncomputable def logToleranceExponent (delta : ℝ) : ℕ :=
  ⌈max 0 (-Real.log delta/Real.log 2)⌉₊

theorem logToleranceExponent_spec (delta : ℝ) (hdelta : 0<delta) :
    ((2:ℝ)^logToleranceExponent delta)⁻¹≤delta ∧
      (logToleranceExponent delta:ℝ)≤max 0 (-Real.log delta/Real.log 2)+1 := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hz : -Real.log delta/Real.log 2≤(logToleranceExponent delta:ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hm := (div_le_iff₀ hlog).mp hz
  constructor
  · apply (Real.log_le_log_iff (by positivity) hdelta).mp
    rw [Real.log_inv,Real.log_pow]
    linarith
  · exact (Nat.ceil_lt_add_one (le_max_left _ _)).le

theorem rational_tolerance_exists (delta : ℚ) (hdelta : 0<delta) :
    ∃ z : ℕ,((2:ℚ)^z)⁻¹≤delta := by
  refine ⟨logToleranceExponent (delta:ℝ),?_⟩
  have hh := (logToleranceExponent_spec (delta:ℝ) (by exact_mod_cast hdelta)).1
  exact Rat.cast_le.mp (show (((((2:ℚ)^logToleranceExponent (delta:ℝ))⁻¹:ℚ):ℝ))≤(delta:ℝ) by
    simpa only [Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hh)

/-- Integer search using exact rational comparisons; no floating-point
logarithm or unspecified sufficiently large precision is evaluated. -/
def rationalToleranceExponent (delta : ℚ) (hdelta : 0<delta) : ℕ :=
  Nat.find (rational_tolerance_exists delta hdelta)

theorem rationalToleranceExponent_spec (delta : ℚ) (hdelta : 0<delta) :
    ((2:ℚ)^rationalToleranceExponent delta hdelta)⁻¹≤delta ∧
    (rationalToleranceExponent delta hdelta:ℝ)≤max 0 (-Real.log (delta:ℝ)/Real.log 2)+1 := by
  refine ⟨Nat.find_spec (rational_tolerance_exists delta hdelta),?_⟩
  have hh := logToleranceExponent_spec (delta:ℝ) (by exact_mod_cast hdelta)
  have hq : ((2:ℚ)^logToleranceExponent (delta:ℝ))⁻¹≤delta :=
    Rat.cast_le.mp (show (((((2:ℚ)^logToleranceExponent (delta:ℝ))⁻¹:ℚ):ℝ))≤(delta:ℝ) by
      simpa only [Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hh.1)
  have hn := Nat.find_min' (rational_tolerance_exists delta hdelta) hq
  change rationalToleranceExponent delta hdelta≤logToleranceExponent (delta:ℝ) at hn
  exact (show (rationalToleranceExponent delta hdelta:ℝ)≤logToleranceExponent (delta:ℝ) by
    exact_mod_cast hn).trans hh.2

end Paper254
#print axioms Paper254.rationalToleranceExponent_spec
#eval Paper254.rationalToleranceExponent (1/1000) (by norm_num)
