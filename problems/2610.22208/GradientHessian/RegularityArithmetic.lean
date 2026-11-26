import GradientHessian.Reliability

/-! Closing the rescaled derivative recurrences by finite geometric sums.
These are arithmetic implications; the actual derivative estimates are separate
inputs to be proved for the literal recursive objective. -/

noncomputable section
namespace GradientHessian.RegularityArithmetic
open scoped BigOperators

theorem sum_decay {r : ℝ} (hr0 : 0≤r) (hr : r<1) (t : ℕ) :
    (∑ j ∈ Finset.range t, r^j) ≤ 1/(1-r) := by
  have he := Reliability.geometric_sum_with_remainder (r := r) t
  apply (le_div_iff₀ (by linarith : 0<1-r)).2
  have hp := pow_nonneg hr0 t
  nlinarith

theorem sum_growth {r : ℝ} (hr : 1<r) (t : ℕ) :
    (∑ j ∈ Finset.range t, r^j) ≤ r^t/(r-1) := by
  have he := Reliability.geometric_sum_with_remainder (r := r) t
  apply (le_div_iff₀ (by linarith : 0<r-1)).2
  nlinarith

theorem accumulate (a inc : ℕ → ℝ) (h : ∀ t, a (t+1) ≤ a t + inc t) (t : ℕ) :
    a t ≤ a 0 + ∑ j ∈ Finset.range t, inc j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hs := h t
    linarith

theorem first_order (a : ℕ → ℝ) {M C : ℝ} (hC : 0≤C)
    (h0 : a 0 ≤ C*M^2)
    (hstep : ∀ t, a (t+1) ≤ a t + C*(M^2*(1/3)^t+(8/3)^t+2^t+1)) (t : ℕ) :
    a t ≤ 4*C*(M^2+(8/3)^t) := by
  have hstep' : ∀ j, a (j+1) ≤ a j + C*(M^2*(1/3)^j+3*(8/3)^j) := by
    intro j
    have h2 : (2:ℝ)^j ≤ (8/3)^j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have h1 : (1:ℝ) ≤ (8/3)^j := one_le_pow₀ (by norm_num)
    have hm := mul_le_mul_of_nonneg_left (show M^2*(1/3)^j+(8/3)^j+2^j+1 ≤
      M^2*(1/3)^j+3*(8/3)^j by linarith) hC
    exact (hstep j).trans (add_le_add_left hm _)
  have ha := accumulate a (fun j => C*(M^2*(1/3)^j+3*(8/3)^j)) hstep' t
  have hs1 := sum_decay (r := 1/3) (by norm_num) (by norm_num) t
  have hs2 := sum_growth (r := 8/3) (by norm_num) t
  norm_num at hs1 hs2
  have hm1 := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hC (sq_nonneg M))
  have hm2 := mul_le_mul_of_nonneg_left hs2 (show 0≤3*C by positivity)
  have hm0 := mul_nonneg hC (sq_nonneg M)
  have hp := mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ)≤8/3) t)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at ha
  nlinarith

theorem second_order (a : ℕ → ℝ) {M C : ℝ} (hM : 0≤M) (hC : 0≤C)
    (h0 : a 0 ≤ C*M)
    (hstep : ∀ t, a (t+1) ≤ a t + C*M*((1/3)^t+(1/9)^t+(8/9)^t+(1/3)^t+(2/3)^t))
    (t : ℕ) : a t ≤ 18*C*M := by
  have ha := accumulate a
    (fun j => C*M*((1/3)^j+(1/9)^j+(8/9)^j+(1/3)^j+(2/3)^j)) hstep t
  have h3 := sum_decay (r := 1/3) (by norm_num) (by norm_num) t
  have h9 := sum_decay (r := 1/9) (by norm_num) (by norm_num) t
  have h89 := sum_decay (r := 8/9) (by norm_num) (by norm_num) t
  have h23 := sum_decay (r := 2/3) (by norm_num) (by norm_num) t
  norm_num at h3 h9 h89 h23
  have hs : (∑ j ∈ Finset.range t,
      ((1/3:ℝ)^j+(1/9)^j+(8/9)^j+(1/3)^j+(2/3)^j)) ≤ 17 := by
    simp only [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum] at ha
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hC hM)
  nlinarith

theorem third_order (a : ℕ → ℝ) {C : ℝ} (hC : 0≤C) (h0 : a 0 ≤ C)
    (hstep : ∀ t, a (t+1) ≤ a t + C*((1/3)^t+(1/9)^t+(1/27)^t+
      (8/27)^t+(2/9)^t+(1/9)^t)) (t : ℕ) : a t ≤ 9*C := by
  have ha := accumulate a
    (fun j => C*((1/3)^j+(1/9)^j+(1/27)^j+(8/27)^j+(2/9)^j+(1/9)^j)) hstep t
  have h3 := sum_decay (r := 1/3) (by norm_num) (by norm_num) t
  have h9 := sum_decay (r := 1/9) (by norm_num) (by norm_num) t
  have h27 := sum_decay (r := 1/27) (by norm_num) (by norm_num) t
  have h827 := sum_decay (r := 8/27) (by norm_num) (by norm_num) t
  have h29 := sum_decay (r := 2/9) (by norm_num) (by norm_num) t
  norm_num at h3 h9 h27 h827 h29
  have hs : (∑ j ∈ Finset.range t,
      ((1/3:ℝ)^j+(1/9)^j+(1/27)^j+(8/27)^j+(2/9)^j+(1/9)^j)) ≤ 8 := by
    simp only [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum] at ha
  have hm := mul_le_mul_of_nonneg_left hs hC
  linarith

end GradientHessian.RegularityArithmetic
