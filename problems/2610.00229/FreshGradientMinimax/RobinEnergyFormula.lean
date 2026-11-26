import FreshGradientMinimax.RobinEdgeEnergy

/-! Literal endpoint and internal edge formulas, and their sum of squares. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem robinEdgeVector_first (n : ℕ) (a b : ℝ) (y : Euclid (n + 2)) :
    (robinIncidence (n + 2) y + robinEdgeShift n a b) 0 =
      y 0 / Real.sqrt (n + 2 : ℕ) - Real.sqrt (robinC (n + 2)) * a := by
  have h0 : Fin.last (n + 2) ≠ (0 : Fin (n + 3)) := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [PiLp.add_apply, robinIncidence_first, robinEdgeShift, PiLp.smul_apply,
    smul_eq_mul, EuclideanSpace.single_apply, if_pos rfl, if_neg h0, if_neg h0.symm, if_true,
    mul_one, mul_zero, add_zero, robinStep, Real.sqrt_inv, div_eq_mul_inv]
  ring

theorem robinEdgeVector_last (n : ℕ) (a b : ℝ) (y : Euclid (n + 2)) :
    (robinIncidence (n + 2) y + robinEdgeShift n a b) (Fin.last (n + 2)) =
      -(y (Fin.last (n + 1)) / Real.sqrt (n + 2 : ℕ) + Real.sqrt (robinC (n + 2)) * b) := by
  have h0 : (0 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [PiLp.add_apply, robinIncidence_last, robinEdgeShift, PiLp.smul_apply,
    smul_eq_mul, EuclideanSpace.single_apply, if_pos rfl, if_neg h0, if_neg h0.symm, if_true,
    mul_one, mul_zero, zero_add, robinStep, Real.sqrt_inv, div_eq_mul_inv]
  ring

theorem robinEdgeVector_interior {n : ℕ} (a b : ℝ) (y : Euclid (n + 2)) (i : Fin (n + 1)) :
    (robinIncidence (n + 2) y + robinEdgeShift n a b) i.succ.castSucc =
      y i.succ - y i.castSucc := by
  have h0 : (0 : Fin (n + 3)) ≠ i.succ.castSucc := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [PiLp.add_apply, robinIncidence_interior, robinEdgeShift, PiLp.smul_apply,
    smul_eq_mul, EuclideanSpace.single_apply, if_neg h0, if_neg h0.symm,
    if_neg (Fin.castSucc_ne_last i.succ).symm, if_neg (Fin.castSucc_ne_last i.succ),
    mul_zero, add_zero]

theorem robinQuadraticEdges_formula (n : ℕ) (a b : ℝ) (y : Euclid (n + 2)) :
    robinQuadraticEdges n a b y =
      ((y 0 / Real.sqrt (n + 2 : ℕ) - Real.sqrt (robinC (n + 2)) * a) ^ 2 +
        (∑ i : Fin (n + 1), (y i.castSucc - y i.succ) ^ 2) +
        (y (Fin.last (n + 1)) / Real.sqrt (n + 2 : ℕ) + Real.sqrt (robinC (n + 2)) * b) ^ 2) / 2 := by
  unfold robinQuadraticEdges
  rw [euclid_norm_sq, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, robinEdgeVector_first, robinEdgeVector_last,
    robinEdgeVector_interior, neg_sq]
  have he : (∑ i : Fin (n + 1), (y i.succ - y i.castSucc) ^ 2) =
      ∑ i : Fin (n + 1), (y i.castSucc - y i.succ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]

end FreshGradientMinimax
