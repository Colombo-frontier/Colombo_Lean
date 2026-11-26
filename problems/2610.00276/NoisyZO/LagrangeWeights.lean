import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Multiscale Lagrange weights

This module formalizes equations (4.5)--(4.6) of `2401.tex`.  The weight at a
node is the corresponding Lagrange basis polynomial evaluated at zero.  Hence
the weighted rule evaluates every polynomial of degree below the number of
nodes at zero; positive monomials vanish and the constant monomial sums to one.
-/

open scoped BigOperators
open Polynomial

namespace NoisyZO

noncomputable section

/-- Lagrange weight for evaluation at zero. -/
def lagrangeWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) : ℝ :=
  (Lagrange.basis Finset.univ node i).eval 0

/-- The basis-at-zero definition is exactly the product formula printed in
the manuscript. -/
theorem lagrangeWeight_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) :
    lagrangeWeight node i =
      ∏ j ∈ Finset.univ.erase i, (-node j) / (node i - node j) := by
  classical
  simp only [lagrangeWeight, Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  apply Finset.prod_congr rfl
  intro j _
  simp [div_eq_mul_inv, mul_comm]

/-- The multiscale weights sum to one. -/
theorem sum_lagrangeWeight_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (node : ι → ℝ) (hinj : Function.Injective node) :
    ∑ i : ι, lagrangeWeight node i = 1 := by
  classical
  have hpoly := Lagrange.sum_basis hinj.injOn (Finset.univ_nonempty : Finset.univ.Nonempty)
  have heval := congrArg (Polynomial.eval (0 : ℝ)) hpoly
  simpa [lagrangeWeight, Polynomial.eval_finsetSum] using heval

/-- Every positive monomial of degree below the node count is cancelled. -/
theorem sum_lagrangeWeight_mul_pow_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hinj : Function.Injective node)
    {ell : ℕ} (hell_pos : 0 < ell) (hell_card : ell < Fintype.card ι) :
    ∑ i : ι, lagrangeWeight node i * (node i) ^ ell = 0 := by
  classical
  let P : ℝ[X] := X ^ ell
  have hdeg : P.degree < (Fintype.card ι : WithBot ℕ) := by
    dsimp [P]
    rw [Polynomial.degree_X_pow]
    exact_mod_cast hell_card
  have hinterp : P = Lagrange.interpolate Finset.univ node (fun i => P.eval (node i)) :=
    Lagrange.eq_interpolate hinj.injOn hdeg
  have heval := congrArg (Polynomial.eval (0 : ℝ)) hinterp
  have hzero : P.eval 0 = 0 := by
    simp [P, hell_pos.ne']
  rw [hzero] at heval
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C] at heval
  calc
    ∑ i : ι, lagrangeWeight node i * (node i) ^ ell =
        ∑ i : ι, P.eval (node i) *
          (Lagrange.basis Finset.univ node i).eval 0 := by
            apply Finset.sum_congr rfl
            intro i _
            simp [lagrangeWeight, P, mul_comm]
    _ = 0 := heval.symm

/-- The paper's nodes `r_j² = 4^{-j}` are pairwise distinct. -/
theorem dyadicSquared_injective (q : ℕ) :
    Function.Injective (fun j : Fin q => (4 : ℝ) ^ (-(j : ℤ))) := by
  intro i j hij
  have hexp : -(i : ℤ) = -(j : ℤ) := by
    exact (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (4 : ℝ) ≠ 1)) hij
  have : (i : ℤ) = (j : ℤ) := by omega
  exact Fin.ext (by exact_mod_cast this)

/-- Moment cancellation for the concrete dyadic squared radii. -/
theorem dyadic_weight_moment_cancellation {J ell : ℕ}
    (hell_pos : 0 < ell) (hell : ell ≤ J) :
    ∑ j : Fin (J + 1),
      lagrangeWeight (fun t : Fin (J + 1) => (4 : ℝ) ^ (-(t : ℤ))) j *
        ((4 : ℝ) ^ (-(j : ℤ))) ^ ell = 0 := by
  apply sum_lagrangeWeight_mul_pow_eq_zero
    (fun t : Fin (J + 1) => (4 : ℝ) ^ (-(t : ℤ)))
    (dyadicSquared_injective (J + 1)) hell_pos
  simpa using Nat.lt_succ_iff.mpr hell

end

end NoisyZO
