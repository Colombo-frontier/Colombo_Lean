import LowRank.InverseGramTailArithmetic
import Mathlib.Tactic

/-! A fractional-moment route to the high-probability square Gaussian
inverse-norm bound needed in the source solve reduction. -/
namespace Matvec
open MeasureTheory Matrix
open scoped Matrix

theorem sqrt_sqrt_eq_quarter (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

theorem gaussian_quarter_moment_le {n : ℕ} (hn : 0 < n) :
    LowRank.gaussianMomentFormula n (1 / 4) ≤ Real.sqrt (Real.sqrt n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := by positivity
  have hf : Integrable (fun x : Fin n → ℝ => Real.sqrt (x ⬝ᵥ x))
      (LowRank.iidVectorLaw n 1) := by
    simpa only [Real.sqrt_eq_rpow] using
      LowRank.gaussian_radial_integrable hn (a := 1 / 2) (by positivity)
  have hg : Integrable (fun x : Fin n → ℝ => Real.sqrt (Real.sqrt (x ⬝ᵥ x)))
      (LowRank.iidVectorLaw n 1) := by
    have heq : (fun x : Fin n → ℝ => Real.sqrt (Real.sqrt (x ⬝ᵥ x))) =
        (fun x => (x ⬝ᵥ x) ^ (1 / 4 : ℝ)) := by
      funext x
      exact sqrt_sqrt_eq_quarter _ (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
    rw [heq]
    exact LowRank.gaussian_radial_integrable hn (by positivity)
  have hpoint (x : Fin n → ℝ) : Real.sqrt (Real.sqrt (x ⬝ᵥ x)) ≤
      (Real.sqrt (x ⬝ᵥ x) + Real.sqrt n) / (2 * Real.sqrt (Real.sqrt n)) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [sq_nonneg (Real.sqrt (Real.sqrt (x ⬝ᵥ x)) - Real.sqrt (Real.sqrt n)),
      Real.sq_sqrt (Real.sqrt_nonneg (x ⬝ᵥ x)),
      Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))]
  have h := integral_mono hg ((hf.add (integrable_const (Real.sqrt (n : ℝ)))).div_const
    (2 * Real.sqrt (Real.sqrt n))) hpoint
  have hint : (∫ x : Fin n → ℝ, Real.sqrt (x ⬝ᵥ x) ∂LowRank.iidVectorLaw n 1) =
      LowRank.gaussianMomentFormula n (1 / 2) := by
    simpa only [Real.sqrt_eq_rpow, LowRank.gaussianMomentFormula] using
      LowRank.gaussian_radial_integral hn (a := 1 / 2) (by positivity)
  have hint' : (∫ x : Fin n → ℝ, Real.sqrt (Real.sqrt (x ⬝ᵥ x))
      ∂LowRank.iidVectorLaw n 1) = LowRank.gaussianMomentFormula n (1 / 4) := by
    convert LowRank.gaussian_radial_integral hn (a := 1 / 4) (by positivity) using 1
    apply integral_congr_ae
    filter_upwards [] with x
    exact sqrt_sqrt_eq_quarter _ (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  simp only [Pi.add_apply] at h
  rw [hint', integral_div, integral_add hf (integrable_const _), hint,
    integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at h
  apply h.trans
  apply (div_le_iff₀ (by positivity)).2
  have hm := LowRank.gaussianMomentFormula_half_le_sqrt hn
  nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))]

noncomputable def squareInverseTailConstant : ℝ :=
  LowRank.gaussianMomentFormula 1 (-(1 / 4)) /
    LowRank.gaussianMomentFormula 1 (1 / 4)

theorem squareInverseTailConstant_pos : 0 < squareInverseTailConstant := by
  exact div_pos (LowRank.gaussianMomentFormula_pos (by norm_num) (by norm_num))
    (LowRank.gaussianMomentFormula_pos (by norm_num) (by norm_num))

theorem square_inverse_moment_bound (n : ℕ) :
    LowRank.inverseGramMomentBound (n + 1) 1 1 (1 / 4) ≤
      squareInverseTailConstant * (n + 1 : ℝ) ^ (1 / 4 : ℝ) := by
  have hp := LowRank.gaussianMomentFormula_pos (m := 1) (a := -(1 / 4))
    (by norm_num) (by norm_num)
  have hd := LowRank.gaussianMomentFormula_pos (m := 1) (a := 1 / 4)
    (by norm_num) (by norm_num)
  have h := gaussian_quarter_moment_le (Nat.succ_pos n)
  rw [sqrt_sqrt_eq_quarter _ (Nat.cast_nonneg _)] at h
  unfold LowRank.inverseGramMomentBound squareInverseTailConstant
  norm_num only [NNReal.coe_one, Real.one_rpow, one_mul]
  have h' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hp.le) hd.le
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, div_mul_eq_mul_div,
    mul_div_assoc, mul_comm] using h'

/-- A dimension-uniform tail for every eigenvalue of the inverse Gram matrix.
For its largest eigenvalue this controls the squared inverse operator norm.
The weaker exponent 1/4 is sufficient for an arbitrarily reliable source
promise; it is not advertised as the sharp linear hard-edge estimate. -/
theorem square_inverse_eigenvalue_tail (n : ℕ) (i : Fin (n + 1))
    (R : ℝ) (hR : 0 < R) :
    (LowRank.iidMatrixLaw (n + 1) (n + 1) 1).real
      {X | R * (n + 1 : ℝ) < LowRank.inverseGramEigenvalue X i} ≤
      squareInverseTailConstant / R ^ (1 / 4 : ℝ) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have ht := LowRank.inverseGram_tail_le_ofReal (d := n + 1) (s := n)
    (v := 1) (by omega) (by norm_num) i (a := 1 / 4) (R := R * (n + 1))
    (by norm_num) (by simp; norm_num) (by positivity)
  have hcoef : LowRank.inverseGramMomentBound (n + 1) ((n + 1) - n) 1 (1 / 4) /
      (R * (n + 1 : ℝ)) ^ (1 / 4 : ℝ) ≤
      squareInverseTailConstant / R ^ (1 / 4 : ℝ) := by
    simp only [Nat.add_sub_cancel_left]
    have h := div_le_div_of_nonneg_right (square_inverse_moment_bound n)
      (Real.rpow_nonneg (le_of_lt (mul_pos hR hn)) (1 / 4))
    refine h.trans_eq ?_
    rw [Real.mul_rpow hR.le hn.le]
    have hnq : (n + 1 : ℝ) ^ (1 / 4 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn _)
    field_simp
    ring
  have hprob := ht.trans (ENNReal.ofReal_le_ofReal hcoef)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
  rw [ENNReal.toReal_ofReal (div_nonneg squareInverseTailConstant_pos.le
    (Real.rpow_nonneg hR.le _))] at h
  exact h

end Matvec
