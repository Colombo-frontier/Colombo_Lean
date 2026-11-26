import RandomizedFO2003.GradientAverage
import RandomizedFO2003.EpochGeometry
import Mathlib.Tactic.Module

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ) (η θ : ℝ) (start : E)

theorem sum_epochMomentum (n : ℕ) :
    ∑ k ∈ Finset.range n, epochMomentum f η θ start k =
      epochPoint f η θ start n - start - epochMomentum f η θ start n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, epochMomentum_succ]
    unfold epochIncrement
    abel

theorem epoch_gradient_step_balance (n : ℕ) :
    η • gradient f (epochQuery f η θ start n) =
      -epochIncrement f η θ start n + (1 - θ) • epochMomentum f η θ start n := by
  change η • gradient f (extrapolate θ (epochState f η θ start n).1 (epochState f η θ start n).2) =
    -(gradientStep η f (extrapolate θ (epochState f η θ start n).1 (epochState f η θ start n).2) -
      (epochState f η θ start n).2) + (1 - θ) • ((epochState f η θ start n).2 - (epochState f η θ start n).1)
  unfold gradientStep extrapolate
  module

theorem sum_epoch_gradients (n : ℕ) :
    η • ∑ k ∈ Finset.range n, gradient f (epochQuery f η θ start k) =
      -θ • (epochPoint f η θ start n - start) - (1 - θ) • epochMomentum f η θ start n := by
  rw [Finset.smul_sum]
  simp_rw [epoch_gradient_step_balance]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.smul_sum,
    sum_epochIncrement, sum_epochMomentum]
  module

theorem sum_epoch_gradients_last (n : ℕ) :
    η • ∑ k ∈ Finset.range (n + 1), gradient f (epochQuery f η θ start k) =
      -epochIncrement f η θ start n - θ • (epochPoint f η θ start n - start) := by
  rw [sum_epoch_gradients, epochMomentum_succ]
  unfold epochIncrement
  module

theorem norm_sum_epoch_gradients_le (hη : 0 < η) (hθ : 0 ≤ θ) (n : ℕ) :
    ‖∑ k ∈ Finset.range (n + 1), gradient f (epochQuery f η θ start k)‖ ≤
      (‖epochIncrement f η θ start n‖ + θ * ‖epochPoint f η θ start n - start‖) / η := by
  have hs := congrArg norm (sum_epoch_gradients_last f η θ start n)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη] at hs
  have hn := norm_sub_le (-epochIncrement f η θ start n) (θ • (epochPoint f η θ start n - start))
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ] at hn
  rw [le_div_iff₀ hη]
  nlinarith

variable {f η θ}

/-- A terminal average bound for the actual accelerated queries. Its inputs
are geometric bounds on this trajectory, not assumed gradient estimates. -/
theorem epoch_average_gradient_bound (hf : ContDiff ℝ 2 f) {ρ R B V : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hη : 0 < η) (hθ : 0 ≤ θ) (n : ℕ)
    (hy : ∀ k < n + 1, ‖epochQuery f η θ start k - start‖ ≤ R)
    (hx : ‖epochPoint f η θ start n - start‖ ≤ B)
    (hv : ‖epochIncrement f η θ start n‖ ≤ V) :
    ‖gradient f (prefixAverage (epochQuery f η θ start) n)‖ ≤
      (V + θ * B) / (η * (n + 1)) + ρ * R ^ 2 := by
  have ha := Calculus.norm_gradient_prefixAverage_le hf hρ hR hH (epochQuery f η θ start) n start hy
  have hs := norm_sum_epoch_gradients_le f η θ start hη hθ n
  have hb : ‖epochIncrement f η θ start n‖ + θ * ‖epochPoint f η θ start n - start‖ ≤ V + θ * B :=
    add_le_add hv (mul_le_mul_of_nonneg_left hx hθ)
  have hs' := hs.trans (div_le_div_of_nonneg_right hb hη.le)
  have hc : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have havg : ‖prefixAverage (fun k => gradient f (epochQuery f η θ start k)) n‖ ≤
      (V + θ * B) / (η * (n + 1)) := by
    unfold prefixAverage
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hc.le)]
    apply (mul_le_mul_of_nonneg_left hs' (inv_nonneg.mpr hc.le)).trans_eq
    push_cast
    field_simp
    exact Or.inl (mul_comm _ _)
  exact ha.trans (add_le_add_right havg _)

end RandomizedFO2003.Accelerated
