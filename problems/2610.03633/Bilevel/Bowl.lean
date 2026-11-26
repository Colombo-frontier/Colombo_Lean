import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The actual coercive scalar wrapper in the small-gap construction. -/
noncomputable section
namespace Bilevel.Bowl
open Filter
open scoped Topology

def value (L x : ℝ) : ℝ := L * (Real.sqrt (1 + x ^ 2) - 1)
def slope (L x : ℝ) : ℝ := L * x / Real.sqrt (1 + x ^ 2)

theorem sqrt_positive (x : ℝ) : 0 < Real.sqrt (1 + x ^ 2) := by positivity
theorem sqrt_square (x : ℝ) : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem hasDerivAt_value (L x : ℝ) : HasDerivAt (value L) (slope L x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have hs := (h1.sqrt (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)).sub_const 1
  convert hs.const_mul L using 1
  unfold slope
  field_simp
  ring

theorem hasDerivAt_slope (L x : ℝ) :
    HasDerivAt (slope L) (L / Real.sqrt (1 + x ^ 2) ^ 3) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have hn : HasDerivAt (fun x : ℝ => L * x) L x := by simpa using (hasDerivAt_id x).const_mul L
  have h := hn.div (h1.sqrt (by positivity)) (sqrt_positive x).ne'
  convert h using 1
  have hc : 2 * x / (2 * Real.sqrt (1 + x ^ 2)) = x / Real.sqrt (1 + x ^ 2) := by
    field_simp
    ring
  rw [hc]
  have hnumer : L * Real.sqrt (1 + x ^ 2) - L * x * (x / Real.sqrt (1 + x ^ 2)) =
      L / Real.sqrt (1 + x ^ 2) := by
    apply (eq_div_iff (sqrt_positive x).ne').mpr
    have hcancel : L * x * (x / Real.sqrt (1 + x ^ 2)) * Real.sqrt (1 + x ^ 2) = L * x ^ 2 := by
      field_simp
      ring
    rw [sub_mul, hcancel]
    nlinarith [congrArg (fun z : ℝ => L * z) (sqrt_square x)]
  rw [hnumer]
  ring

theorem nonnegative (L x : ℝ) (hL : 0 ≤ L) : 0 ≤ value L x := by
  have hs : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [sq_nonneg x, sqrt_square x, sqrt_positive x]
  exact mul_nonneg hL (sub_nonneg.mpr hs)

theorem quadratic_upper (L x : ℝ) (hL : 0 ≤ L) : value L x ≤ L * x ^ 2 / 2 := by
  have hs : Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 / 2 := by
    have hp := sqrt_positive x
    nlinarith [sqrt_square x, sq_nonneg (x ^ 2)]
  have h := mul_le_mul_of_nonneg_left hs hL
  dsimp [value]
  nlinarith

theorem slope_bound (L x : ℝ) (hL : 0 ≤ L) : |slope L x| ≤ L := by
  have hx : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [sq_abs x, sqrt_square x, sqrt_positive x, abs_nonneg x]
  unfold slope
  rw [abs_div, abs_mul, abs_of_nonneg hL, abs_of_pos (sqrt_positive x)]
  apply (div_le_iff₀ (sqrt_positive x)).mpr
  exact mul_le_mul_of_nonneg_left hx hL

theorem slope_positive (L x : ℝ) (hL : 0 < L) (hx : 0 < x) : 0 < slope L x := by
  unfold slope
  positivity

theorem curvature_bounds (L x : ℝ) (hL : 0 < L) :
    0 < deriv (slope L) x ∧ deriv (slope L) x ≤ L := by
  rw [(hasDerivAt_slope L x).deriv]
  have hs : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [sq_nonneg x, sqrt_square x, sqrt_positive x]
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (1 + x ^ 2) ^ 3)).mpr
    have hp : 1 ≤ Real.sqrt (1 + x ^ 2) ^ 3 := one_le_pow₀ hs
    nlinarith

theorem slope_monotone (L : ℝ) (hL : 0 < L) : Monotone (slope L) := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_slope L x).differentiableAt)
  intro x
  exact (curvature_bounds L x hL).1.le

theorem slope_local_lower (L x : ℝ) (hL : 0 ≤ L) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    L * x / 2 ≤ slope L x := by
  have hs : Real.sqrt (1 + x ^ 2) ≤ 2 := by
    nlinarith [sqrt_square x, sqrt_positive x, hx.1, hx.2]
  exact div_le_div_of_nonneg_left (mul_nonneg hL hx.1) (sqrt_positive x) hs

theorem coercive (L : ℝ) (hL : 0 < L) : Tendsto (value L) (cocompact ℝ) atTop := by
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop (b / L + 1)
  filter_upwards [hn] with x hx
  have hs : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [sq_abs x, sqrt_square x, sqrt_positive x, abs_nonneg x]
  rw [Real.norm_eq_abs] at hx
  have hb : b ≤ L * (|x| - 1) := by
    have h := (div_le_iff₀ hL).mp (show b / L ≤ |x| - 1 by linarith)
    nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left (by linarith) hL.le)

end Bilevel.Bowl
