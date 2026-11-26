import Bilevel.ZeroChainGate
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The article's exact zero-chain activation profile

`psi` is the displayed piecewise exponential, including its original threshold
and normalization. Smoothness, all flat jets, and all fixed-order uniform
bounds follow from the exact one-sided Gaussian gate proved separately.
-/

noncomputable section
open Real

namespace Bilevel.ZeroChainProfiles
open ZeroChainGate

def psi (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then 0 else Real.exp (1 - ((2 * t - 1)⁻¹) ^ 2)

theorem psi_eq_gate (t : ℝ) : psi t = Real.exp 1 * gate (2 * t - 1) := by
  by_cases ht : t ≤ 1 / 2
  · simp only [psi, if_pos ht, gate_zero (by linarith : 2 * t - 1 ≤ 0), mul_zero]
  · rw [psi, if_neg ht, gate_pos_formula (by linarith : 0 < 2 * t - 1), ← Real.exp_add]
    congr 1

theorem psi_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) : psi t = 0 := by simp only [psi, if_pos ht]

theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := by
  rw [psi_eq_gate]
  exact mul_nonneg (Real.exp_pos _).le (gate_nonneg _)

theorem psi_pos_of_gt {t : ℝ} (ht : 1 / 2 < t) : 0 < psi t := by
  rw [psi, if_neg ht.not_le]
  exact Real.exp_pos _

theorem psi_le_exp_one (t : ℝ) : psi t ≤ Real.exp 1 := by
  rw [psi_eq_gate]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (gate_le_one _)

theorem psi_one : psi 1 = 1 := by norm_num [psi]

theorem psi_contDiff {n : ℕ∞} : ContDiff ℝ n psi := by
  have he : psi = fun t => Real.exp 1 * gate (2 * t - 1) := funext psi_eq_gate
  rw [he]
  exact contDiff_const.mul (gate_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem psi_hasDerivAt (t : ℝ) :
    HasDerivAt psi (4 * ((2 * t - 1)⁻¹) ^ 3 * psi t) t := by
  have h := ((gate_hasDerivAt (2 * t - 1)).comp t
    (((hasDerivAt_id t).const_mul 2).sub_const 1)).const_mul (Real.exp 1)
  convert h using 1
  · exact funext psi_eq_gate
  · rw [psi_eq_gate]
    ring

theorem psi_deriv (t : ℝ) : deriv psi t = 4 * ((2 * t - 1)⁻¹) ^ 3 * psi t :=
  (psi_hasDerivAt t).deriv

theorem psi_deriv_nonneg (t : ℝ) : 0 ≤ deriv psi t := by
  rw [psi_deriv]
  by_cases ht : t ≤ 1 / 2
  · simp only [psi_zero_of_le ht, mul_zero, le_refl]
  · have hx : 0 < 2 * t - 1 := by linarith
    exact mul_nonneg (by positivity) (psi_nonneg t)

theorem psi_monotone : Monotone psi :=
  monotone_of_deriv_nonneg (fun t => (psi_hasDerivAt t).differentiableAt) psi_deriv_nonneg

theorem psi_ge_one {t : ℝ} (ht : 1 ≤ t) : 1 ≤ psi t := by
  simpa only [psi_one] using psi_monotone ht

theorem psi_iteratedDeriv (n : ℕ) (t : ℝ) :
    iteratedDeriv n psi t = Real.exp 1 * 2 ^ n * iteratedDeriv n gate (2 * t - 1) := by
  have he : psi = fun t => Real.exp 1 * gate (2 * t - 1) := funext psi_eq_gate
  have hc : ContDiff ℝ n (fun t : ℝ => gate (2 * t - 1)) :=
    gate_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hs : ContDiff ℝ n (fun t : ℝ => gate (t + -1)) :=
    gate_contDiff.comp (contDiff_id.add contDiff_const)
  rw [he, iteratedDeriv_const_mul hc.contDiffAt]
  have hscaled := congrFun (iteratedDeriv_comp_const_mul hs (2 : ℝ)) t
  rw [iteratedDeriv_comp_add_const] at hscaled
  simp only [sub_eq_add_neg] at ⊢
  rw [hscaled]
  ring

theorem psi_iteratedDeriv_zero_of_le (n : ℕ) {t : ℝ} (ht : t ≤ 1 / 2) :
    iteratedDeriv n psi t = 0 := by
  rw [psi_iteratedDeriv, gate_flat n (by linarith : 2 * t - 1 ≤ 0), mul_zero]

theorem psi_deriv_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) : deriv psi t = 0 := by
  simpa only [iteratedDeriv_one] using psi_iteratedDeriv_zero_of_le 1 ht

theorem psi_deriv2_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) : deriv (deriv psi) t = 0 := by
  simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] using
    psi_iteratedDeriv_zero_of_le 2 ht

theorem psi_deriv3_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    deriv (deriv (deriv psi)) t = 0 := by
  simpa only [show (3 : ℕ) = (1 + 1) + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] using
    psi_iteratedDeriv_zero_of_le 3 ht

/-- Every fixed-order derivative of the original activation is globally bounded. -/
theorem psi_derivative_bounded (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |iteratedDeriv n psi t| ≤ K := by
  obtain ⟨K, hK, hb⟩ := gate_derivative_bounded n
  refine ⟨Real.exp 1 * 2 ^ n * K, by positivity, fun t => ?_⟩
  rw [psi_iteratedDeriv, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp 1 * 2 ^ n)]
  exact mul_le_mul_of_nonneg_left (hb (2 * t - 1)) (by positivity)

/-- One universal constant controls the function and its first three derivatives. -/
theorem psi_common_bound : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (j : Fin 4) (t : ℝ), |iteratedDeriv j.val psi t| ≤ K := by
  classical
  choose K hK hb using (fun j : Fin 4 => psi_derivative_bounded j.val)
  refine ⟨1 + ∑ j, K j, ?_, fun j t => ?_⟩
  · have hsum : 0 ≤ ∑ j, K j := Finset.sum_nonneg (fun j _ => hK j)
    linarith
  · have hj : K j ≤ ∑ i, K i := Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ j)
    exact (hb j t).trans (by linarith)

end Bilevel.ZeroChainProfiles
