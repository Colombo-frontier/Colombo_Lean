import RandomizedFO2003.EpochQuadratic

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {η θ : ℝ} (start : E)

theorem epoch_taylor_error_le (hf : ContDiff ℝ 2 f) {ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ)
    (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2) :
    ‖epochTaylorError f η θ start n‖ ≤ 2 * ρ * B ^ 2 := by
  have hy := (epoch_geometry_of_restart_budget f η θ start hB hθ hθ1 n hbudget).2.2
  have hs := Calculus.norm_gradient_linearization_error_le hf hH start (epochQuery f η θ start n)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * B)).mpr hy
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ρ / 2 by positivity)
  change ‖epochTaylorError f η θ start n‖ ≤ _ at hs
  nlinarith

/-- All errors used by the terminal step are bounded by the preterminal
restart budget, because that budget is monotone along an epoch. -/
theorem epoch_taylor_error_sum_le (hf : ContDiff ℝ 2 f) {ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ)
    (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2) :
    (∑ k ∈ Finset.range (n + 1), ‖epochTaylorError f η θ start k‖ ^ 2) ≤
      4 * ρ ^ 2 * B ^ 4 * (n + 1 : ℕ) := by
  have hk (k : ℕ) (hkn : k ∈ Finset.range (n + 1)) :
      ‖epochTaylorError f η θ start k‖ ^ 2 ≤ 4 * ρ ^ 2 * B ^ 4 := by
    have hle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkn)
    have hb := (epoch_restart_budget_mono f η θ start hle).trans hbudget
    have hh := epoch_taylor_error_le start hf hρ hB hH hθ hθ1 k hb
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ρ * B ^ 2)).mpr hh
    nlinarith
  simpa [mul_comm] using Finset.sum_le_sum hk

variable [FiniteDimensional ℝ E]

/-- Small-last-gradient decrease for the actual nonlinear epoch, obtained
by summing spectral certificates and adding the cubic Taylor remainder. -/
theorem small_gradient_epoch_decrease (hf : ContDiff ℝ 2 f) {ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hη : 0 < η) (hnorm : η * ‖fderiv ℝ (gradient f) start‖ ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (n : ℕ)
    (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2)
    (hsmall : η * ‖gradient f (epochQuery f η θ start n)‖ ≤ B) :
    f (epochPoint f η θ start (n + 1)) - f start ≤
      -(3 * θ / (8 * η)) * epochEnergy f η θ start (n + 1) +
        8 * η * ρ ^ 2 * B ^ 4 * (n + 1 : ℕ) / θ + (9 / 2) * ρ * B ^ 3 := by
  have hq := epoch_quadratic_decrease start hf hη hnorm hθ hθ1 (n + 1)
  have he := epoch_taylor_error_sum_le start hf hρ hB hH hθ.le hθ1 n hbudget
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * η / θ by positivity)
  have hr := epoch_terminal_radius_of_small_gradient f η θ start hB hη.le hθ.le hθ1 n hbudget hsmall
  have ht := Calculus.abs_quadratic_error_le hf hH start (epochPoint f η θ start (n + 1))
  have hcube := pow_le_pow_left₀ (norm_nonneg (epochPoint f η θ start (n + 1) - start)) hr 3
  have hc := mul_le_mul_of_nonneg_left hcube (show 0 ≤ ρ / 6 by positivity)
  have ht' := (le_abs_self _).trans ht
  unfold vectorQuadratic at hq
  have heq : (2 * η / θ) * (4 * ρ ^ 2 * B ^ 4 * (n + 1 : ℕ)) =
      8 * η * ρ ^ 2 * B ^ 4 * (n + 1 : ℕ) / θ := by ring
  rw [heq] at he'
  nlinarith

end RandomizedFO2003.Accelerated
