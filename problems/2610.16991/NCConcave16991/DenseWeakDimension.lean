import NCConcave16991.DenseWeakAlignmentArithmetic
import Mathlib.Tactic.Ring

/-! # A concrete finite dimension satisfying all alignment calibrations

Only finiteness is required in the oracle model, so a simple polynomial
dimension avoids rounding logarithms without altering any query bound.
-/

namespace NCConcave16991.DenseWeakHiding

def alignmentDimension (budget stages : ℕ) : ℕ := 1048576 * (budget + 1) * (stages + 1)

theorem alignmentDimension_pos (budget stages : ℕ) : 0 < alignmentDimension budget stages := by
  unfold alignmentDimension
  positivity

theorem alignmentDimension_cast (budget stages : ℕ) :
    (alignmentDimension budget stages : ℝ) =
      1048576 * ((budget : ℝ) + 1) * ((stages : ℝ) + 1) := by
  simp only [alignmentDimension, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

theorem alignmentDimension_information (budget stages : ℕ) :
    512 * Real.log ((budget : ℝ) + 2) + 2048 ≤ (alignmentDimension budget stages : ℝ) := by
  rw [alignmentDimension_cast]
  have hb : (1 : ℝ) ≤ (budget : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ budget by positivity]
  have hs : (1 : ℝ) ≤ (stages : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ stages by positivity]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (budget : ℝ) + 2)
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1048576 * ((budget : ℝ) + 1))
  nlinarith

theorem alignmentDimension_future_tail (budget stages : ℕ) :
    ((budget : ℝ) + 1) * (stages : ℝ) *
      Real.exp (-25 * (alignmentDimension budget stages : ℝ) / 2048) ≤ 1 / 128 := by
  rw [show -25 * (alignmentDimension budget stages : ℝ) / 2048 =
      -(25 * (alignmentDimension budget stages : ℝ) / 2048) by ring, Real.exp_neg,
    ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have he := Real.add_one_le_exp (25 * (alignmentDimension budget stages : ℝ) / 2048)
  rw [alignmentDimension_cast] at he
  rw [alignmentDimension_cast]
  have hprod : (0 : ℝ) ≤ ((budget : ℝ) + 1) * (stages : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ (budget : ℝ) + 1 := by positivity
  nlinarith

end NCConcave16991.DenseWeakHiding
