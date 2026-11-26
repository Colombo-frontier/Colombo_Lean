import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

namespace SecondOrder
noncomputable section

/-- KL of the biased ±R sign channel against the fair law, in terms of bias u. -/
def signKL (u : ℝ) : ℝ := ((1+u)*Real.log (1+u)+(1-u)*Real.log (1-u))/2

theorem signKL_le_sq {u : ℝ} (hu : |u| < 1) : signKL u ≤ u^2 := by
  have hu1 : 0 < 1+u := by have := (abs_lt.mp hu).1; linarith
  have hu2 : 0 < 1-u := by have := (abs_lt.mp hu).2; linarith
  have hp := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu1) hu1.le
  have hm := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu2) hu2.le
  unfold signKL
  nlinarith

theorem biased_sign_entropy {R c : ℝ} (hR : 2 ≤ R) (hc : c^2=1) :
    signKL (c/R) ≤ 1/R^2 := by
  have hRp : 0 < R := by linarith
  have hac : |c| = 1 := by nlinarith [sq_abs c, abs_nonneg c]
  have hu : |c/R| < 1 := by
    rw [abs_div, hac, abs_of_pos hRp]
    exact (div_lt_one hRp).mpr (by linarith)
  have h := signKL_le_sq hu
  simpa only [div_pow, hc] using h

theorem biased_sign_probability_and_mean {R c : ℝ} (hR : 2 ≤ R) (hc : c^2=1) :
    0 < (1+c/R)/2 ∧ (1+c/R)/2 < 1 ∧
      ((1+c/R)/2)*R+(1-(1+c/R)/2)*(-R) = c := by
  have hRp : 0 < R := by linarith
  have hac : |c| = 1 := by nlinarith [sq_abs c, abs_nonneg c]
  have hb : |c/R| < 1 := by
    rw [abs_div, hac, abs_of_pos hRp]
    exact (div_lt_one hRp).mpr (by linarith)
  constructor
  · have := (abs_lt.mp hb).1; linarith
  constructor
  · have := (abs_lt.mp hb).2; linarith
  · field_simp [ne_of_gt hRp]
    <;> ring

/-- Finite binary relative entropy, used only for reference probabilities
strictly between zero and one. Boundary support cases are separate. -/
def binaryKL (p q : ℝ) : ℝ :=
  p*Real.log p+(1-p)*Real.log (1-p)-p*Real.log q-(1-p)*Real.log (1-q)

theorem binary_entropy_lower {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    p*Real.log (1/q)-Real.log 2 ≤ binaryKL p q := by
  have hh := Real.binEntropy_le_log_two (p := p)
  have hlog : Real.log (1-q) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hm := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1-p) hlog
  simp only [Real.binEntropy, Real.log_inv] at hh
  rw [one_div, Real.log_inv]
  unfold binaryKL
  nlinarith

theorem rare_event_probability_bound {p q K A : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hKL : binaryKL p q ≤ K)
    (hA : 0 < A) (hrare : A ≤ Real.log (1/q)) : p ≤ (K+Real.log 2)/A := by
  have h := binary_entropy_lower hp0 hp1 hq0 hq1
  have hm := mul_le_mul_of_nonneg_left hrare hp0
  apply (le_div_iff₀ hA).mpr
  nlinarith

end
end SecondOrder
