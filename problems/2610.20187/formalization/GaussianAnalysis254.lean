import Audit254
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-! Analytic identities for explicit Gaussian formulas. Their identification
with measure-theoretic Gaussian KL and integrals is proved in
GaussianMatrixKL254, GaussianIsotropy254, and GaussianLinear254. -/
noncomputable section
open scoped BigOperators
namespace Paper254

def covariancePenalty (q c : ℝ) : ℝ := q / c - 1 + Real.log (c / q)
def coordinateKL (q c r : ℝ) : ℝ := (covariancePenalty q c + r ^ 2 / c) / 2

theorem covariancePenalty_nonneg (q c : ℝ) (hq : 0 < q) (hc : 0 < c) :
    0 ≤ covariancePenalty q c := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hq hc)
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hc)] at hl
  unfold covariancePenalty
  rw [Real.log_div (ne_of_gt hc) (ne_of_gt hq)]
  linarith

theorem coordinateKL_nonneg (q c r : ℝ) (hq : 0 < q) (hc : 0 < c) :
    0 ≤ coordinateKL q c r := by
  exact div_nonneg (add_nonneg (covariancePenalty_nonneg q c hq hc)
    (div_nonneg (sq_nonneg r) (le_of_lt hc))) (by norm_num)

/-- Covariance flooring is proved by its explicit eigen-coordinate formula,
without a derivative monotonicity assumption. -/
theorem coordinateKL_floor (q c r : ℝ) (hq : 0 < q) (hc : 0 < c) :
    coordinateKL q (max c q) r ≤ coordinateKL q c r := by
  by_cases h : c ≤ q
  · rw [max_eq_right h]
    have hp := covariancePenalty_nonneg q c hq hc
    have hd : r ^ 2 / q ≤ r ^ 2 / c := div_le_div_of_nonneg_left (sq_nonneg r) hc h
    have he : covariancePenalty q q = 0 := by simp [covariancePenalty, ne_of_gt hq]
    unfold coordinateKL
    rw [he]
    linarith
  · rw [max_eq_left (le_of_not_ge h)]

theorem diagonalKL_floor {ι : Type*} [Fintype ι]
    (q : ℝ) (c r : ι → ℝ) (hq : 0 < q) (hc : ∀ i, 0 < c i) :
    (∑ i, coordinateKL q (max (c i) q) (r i)) ≤
      ∑ i, coordinateKL q (c i) (r i) := by
  exact Finset.sum_le_sum (fun i _ => coordinateKL_floor q (c i) (r i) hq (hc i))

theorem log_one_add_lower (s : ℝ) (hs : 0 ≤ s) :
    s / (1+s) ≤ Real.log (1+s) := by
  have hp : 0 < 1+s := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have he : 1 - (1+s)⁻¹ = s/(1+s) := by field_simp; ring
  rw [he] at hl
  exact hl

theorem gaussian_gap_formula_nonpos (s a : ℝ) (hs : 0 ≤ s)
    (ha : |a| ≤ 1/4) :
    -Real.log (1+s)/2 + s*(1+a)^2/(4*(1+s)) ≤ 0 := by
  have hab := abs_le.mp ha
  have hq : (1+a)^2 ≤ 25/16 := by nlinarith [sq_nonneg (a+1/4)]
  have hb := Audit254.gaussian_mix_sign s ((1+a)^2) (Real.log (1+s)) hs hq
    (log_one_add_lower s hs)
  have hn : -7*s/(64*(1+s)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  exact le_trans hb hn

/-- The square-root movement inequality for the full quadratic potential.
For Gaussian KL, Q is Sigma^{-1/2}/sqrt(2), and c is the covariance term.
The spectral identification and the bound on norm Q remain separate. -/
theorem quadratic_potential_movement {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Q : E →L[ℝ] E) (m u v : E) (c : ℝ) (hc : 0 ≤ c) :
    Real.sqrt (c + ‖Q (v-m)‖^2) ≤
      Real.sqrt (c + ‖Q (u-m)‖^2) + ‖Q‖ * ‖v-u‖ := by
  have he : Q (v-m) = Q (u-m) + Q (v-u) := by
    rw [← map_add]
    congr 1
    abel
  have hn : ‖Q (v-m)‖ ≤ ‖Q (u-m)‖ + ‖Q‖ * ‖v-u‖ := by
    rw [he]
    exact le_trans (norm_add_le _ _)
      (add_le_add_left (Q.le_opNorm _) _)
  have hroot : Real.sqrt (‖Q (v-m)‖^2) ≤
      Real.sqrt (‖Q (u-m)‖^2) + ‖Q‖ * ‖v-u‖ := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hn
  have h := Audit254.sqrt_shift (‖Q (v-m)‖^2) (‖Q (u-m)‖^2) c
    (‖Q‖ * ‖v-u‖) (sq_nonneg _) (sq_nonneg _) hc (by positivity) hroot
  simpa only [add_comm (‖Q (v-m)‖^2) c, add_comm (‖Q (u-m)‖^2) c] using h

end Paper254
#print axioms Paper254.diagonalKL_floor
#print axioms Paper254.gaussian_gap_formula_nonpos
#print axioms Paper254.quadratic_potential_movement
