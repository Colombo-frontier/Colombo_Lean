import NoisyZO.LagrangeWeights
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Algebraic core of the multiscale estimator

This module formalizes the cancellation argument in Proposition 4.1.  It is
independent of how the single-scale means and Taylor remainders are produced.
Once an expansion contains a constant term, finitely many powers of the
squared radius, and a remainder, the Lagrange moment identities remove every
explicit power exactly.
-/

open scoped BigOperators

namespace NoisyZO

theorem weighted_expansion_cancellation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {J : ℕ} (weight node : ι → ℝ)
    (hsum : ∑ j : ι, weight j = 1)
    (hmoment : ∀ ell : Fin J,
      ∑ j : ι, weight j * (node j) ^ (ell.val + 1) = 0)
    (mean err : ι → E) (g : E) (coeff : Fin J → E)
    (hexpansion : ∀ j,
      mean j = g +
        (∑ ell : Fin J, (node j) ^ (ell.val + 1) • coeff ell) + err j) :
    (∑ j : ι, weight j • mean j) =
      g + ∑ j : ι, weight j • err j := by
  simp_rw [hexpansion, smul_add, Finset.sum_add_distrib]
  have hconstant : (∑ j : ι, weight j • g) = g := by
    rw [← Finset.sum_smul, hsum, one_smul]
  have hpolynomial :
      (∑ j : ι, weight j •
        ∑ ell : Fin J, (node j) ^ (ell.val + 1) • coeff ell) = 0 := by
    calc
      (∑ j : ι, weight j •
          ∑ ell : Fin J, (node j) ^ (ell.val + 1) • coeff ell) =
          ∑ j : ι, ∑ ell : Fin J,
            (weight j * (node j) ^ (ell.val + 1)) • coeff ell := by
              apply Finset.sum_congr rfl
              intro j _
              simp [Finset.smul_sum, smul_smul]
      _ = ∑ ell : Fin J, ∑ j : ι,
            (weight j * (node j) ^ (ell.val + 1)) • coeff ell := Finset.sum_comm
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro ell _
            rw [← Finset.sum_smul, hmoment ell, zero_smul]
  rw [hconstant, hpolynomial, add_zero]

/-- Norm bound for the remaining weighted Taylor errors. -/
theorem weighted_remainder_norm_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (weight : ι → ℝ) (err : ι → E) (bound : ι → ℝ)
    (hbound : ∀ j, ‖err j‖ ≤ bound j) :
    ‖∑ j : ι, weight j • err j‖ ≤
      ∑ j : ι, |weight j| * bound j := by
  calc
    ‖∑ j : ι, weight j • err j‖ ≤
        ∑ j : ι, ‖weight j • err j‖ := norm_sum_le _ _
    _ = ∑ j : ι, |weight j| * ‖err j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j : ι, |weight j| * bound j := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hbound j) (abs_nonneg _)

/-- Bias theorem obtained by combining exact cancellation with the remainder
bound. -/
theorem multiscale_bias_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℕ} (weight node : ι → ℝ)
    (hsum : ∑ j : ι, weight j = 1)
    (hmoment : ∀ ell : Fin J,
      ∑ j : ι, weight j * (node j) ^ (ell.val + 1) = 0)
    (mean err : ι → E) (g : E) (coeff : Fin J → E)
    (hexpansion : ∀ j,
      mean j = g +
        (∑ ell : Fin J, (node j) ^ (ell.val + 1) • coeff ell) + err j)
    (bound : ι → ℝ) (hbound : ∀ j, ‖err j‖ ≤ bound j) :
    ‖(∑ j : ι, weight j • mean j) - g‖ ≤
      ∑ j : ι, |weight j| * bound j := by
  rw [weighted_expansion_cancellation weight node hsum hmoment mean err g coeff
    hexpansion]
  simp only [add_sub_cancel_left]
  exact weighted_remainder_norm_bound weight err bound hbound

end NoisyZO
