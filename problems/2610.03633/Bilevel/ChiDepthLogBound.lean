import Bilevel.ChiIndependentWidths

/-! Every fixed exponential loss in the actual log-log depth is bounded
by a fixed power of the source logarithm. Constants precede public budgets. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths

theorem chosenDepth_add_one_bound {θ : ℝ} (hθ : 1 ≤ θ) :
    (chosenDepth θ:ℝ)+1 ≤ 2*Real.log (2+θ) := by
  have hd := chosenDepth_bound hθ
  have hs := depth_sq_le_pow (chosenDepth θ)
  have ho : (1:ℝ) ≤ 4^chosenDepth θ := one_le_pow₀ (by norm_num)
  cases hJ : chosenDepth θ with
  | zero => simp only [hJ,Nat.cast_zero,pow_zero] at hd ⊢; linarith
  | succ j =>
    have hj : (1:ℝ) ≤ chosenDepth θ := by rw [hJ]; norm_num
    rw [hJ] at hd hs ho hj
    nlinarith only [hd,hs,ho,hj]

theorem exists_depth_power_log_bound {C : ℝ} (hC : 0 ≤ C) :
    ∃ q : ℕ,∀ θ : ℝ,1 ≤ θ → C^chosenDepth θ ≤ (Real.log (2+θ))^q := by
  obtain ⟨q,hq⟩ := pow_unbounded_of_one_lt C (by norm_num : (1:ℝ)<4)
  refine ⟨q,fun θ hθ => ?_⟩
  have hh := pow_le_pow_left₀ hC hq.le (chosenDepth θ)
  calc
    _ ≤ ((4:ℝ)^q)^chosenDepth θ := hh
    _ = ((4:ℝ)^chosenDepth θ)^q := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ (Real.log (2+θ))^q := pow_le_pow_left₀ (by positivity) (chosenDepth_bound hθ) q

theorem exists_depth_polynomial_log_bound {C : ℝ} (hC : 0 ≤ C) (p : ℕ) :
    ∃ q : ℕ,∀ θ : ℝ,1 ≤ θ →
      C^chosenDepth θ*((chosenDepth θ:ℝ)+1)^p ≤ 2^p*(Real.log (2+θ))^(q+p) := by
  obtain ⟨q,hq⟩ := exists_depth_power_log_bound hC
  refine ⟨q,fun θ hθ => ?_⟩
  have hdepth := chosenDepth_add_one_bound hθ
  have hlog : 0 ≤ Real.log (2+θ) := Real.log_nonneg (by linarith)
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (chosenDepth θ:ℝ)+1) hdepth p
  have hh := mul_le_mul (hq θ hθ) hp (by positivity) (by positivity)
  apply hh.trans_eq
  rw [mul_pow,pow_add]
  ring

end Bilevel.ChiIndependentWidths
