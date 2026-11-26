import FreshGradientMinimax.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Scalar decision-region algebra in Appendix D. The actual clipped globally
admissible family and its transcript KL bound are not formalized in this file. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def testingSlopePlus (L μ : ℝ) : ℝ := L / 16 + (L / 16) ^ 2 / (5 * μ)
def testingSlopeMinus (L μ : ℝ) : ℝ := L / 16 + (L / 16) ^ 2 / (7 * μ)

theorem testing_slopes_ordered {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) :
    0 < testingSlopeMinus L μ ∧ testingSlopeMinus L μ < testingSlopePlus L μ := by
  constructor
  · unfold testingSlopeMinus
    positivity
  · unfold testingSlopeMinus testingSlopePlus
    have hd : (L / 16) ^ 2 / (7 * μ) < (L / 16) ^ 2 / (5 * μ) := by
      apply div_lt_div_of_pos_left (by positivity) (by positivity)
      linarith
    linarith

def testingOffset (qPlus qMinus ε : ℝ) : ℝ := 2 * ε * (qPlus + qMinus) / (qPlus - qMinus)
def successfulInterval (q d ε : ℝ) : Set ℝ := {x | |q * x + d| ≤ ε}

theorem successfulInterval_eq {q : ℝ} (hq : 0 < q) (d ε : ℝ) :
    successfulInterval q d ε = Set.Icc ((-d - ε) / q) ((-d + ε) / q) := by
  ext x
  simp only [successfulInterval, Set.mem_setOf_eq, Set.mem_Icc, abs_le,
    div_le_iff₀ hq, le_div_iff₀ hq]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- The two successful regions in D.1 are disjoint when their derivatives
have the stated affine form. -/
theorem testing_intervals_disjoint {qPlus qMinus ε : ℝ}
    (hm : 0 < qMinus) (hpm : qMinus < qPlus) (hε : 0 < ε) :
    Disjoint (successfulInterval qPlus (testingOffset qPlus qMinus ε) ε)
      (successfulInterval qMinus (testingOffset qPlus qMinus ε) ε) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change |qPlus * x + testingOffset qPlus qMinus ε| ≤ ε at hx
  change |qMinus * x + testingOffset qPlus qMinus ε| ≤ ε at hy
  obtain ⟨hxlo, _⟩ := abs_le.mp hx
  obtain ⟨_, hyhi⟩ := abs_le.mp hy
  have hp : 0 < qPlus := hm.trans hpm
  have h1 := mul_le_mul_of_nonneg_left hxlo hm.le
  have h2 := mul_le_mul_of_nonneg_left hyhi hp.le
  have hden : qPlus - qMinus ≠ 0 := ne_of_gt (sub_pos.mpr hpm)
  have hid : testingOffset qPlus qMinus ε * (qPlus - qMinus) =
      2 * ε * (qPlus + qMinus) := by
    unfold testingOffset
    field_simp
  have hpos : 0 < ε * (qPlus + qMinus) := by positivity
  nlinarith

/-- The offset constants in Appendix D simplify to an explicit expression. -/
theorem testing_offset_formula {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (ε : ℝ) :
    testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε =
      ε * (12 + 1120 * μ / L) := by
  have hord := testing_slopes_ordered hL hμ
  have hd : testingSlopePlus L μ - testingSlopeMinus L μ ≠ 0 :=
    ne_of_gt (sub_pos.mpr hord.2)
  unfold testingOffset
  apply (div_eq_iff hd).mpr
  unfold testingSlopePlus testingSlopeMinus
  field_simp
  ring

theorem testing_offset_bounds {L μ ε : ℝ} (hL : 0 < L) (hμ : 0 < μ)
    (hκ : 1120 * μ ≤ L) (hε : 0 ≤ ε) :
    12 * ε ≤ testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε ∧
      testingOffset (testingSlopePlus L μ) (testingSlopeMinus L μ) ε ≤ 13 * ε := by
  rw [testing_offset_formula hL hμ]
  have hl : 0 ≤ 1120 * μ / L := by positivity
  have hu : 1120 * μ / L ≤ 1 := (div_le_one hL).mpr hκ
  constructor <;> nlinarith

/-- Explicit zero-gradient point and gap of each quadratic local value model. -/
theorem local_quadratic_gap {q : ℝ} (hq : 0 < q) (d x : ℝ) :
    q / 2 * x ^ 2 + d * x + d ^ 2 / (2 * q) = q / 2 * (x + d / q) ^ 2 := by
  field_simp
  ring

theorem local_quadratic_derivative (q d x : ℝ) :
    HasDerivAt (fun t => q / 2 * t ^ 2 + d * t) (q * x + d) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul (q / 2)).add
    ((hasDerivAt_id x).const_mul d) using 1
  simp only [id_eq]
  ring

end FreshGradientMinimax
