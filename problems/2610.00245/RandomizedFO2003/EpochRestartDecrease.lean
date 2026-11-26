import RandomizedFO2003.EpochSmallGradient

namespace RandomizedFO2003.Accelerated

variable {ρ B η θ K S : ℝ}

/-- Algebraic parameter conditions sufficient for a uniform restart decrease.
They will later be discharged by the rounded epoch length. -/
theorem restart_model_bound (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hη : 0 < η) (hθ : 0 < θ)
    (hK : 0 ≤ K) (hlength : θ * K ≤ 1) (henergy : θ * B ^ 2 ≤ S)
    (hscale : 16 * ρ * B * η ≤ θ ^ 2) :
    -(3 * θ / (8 * η)) * S + 8 * η * ρ ^ 2 * B ^ 4 * K / θ +
      (9 / 2) * ρ * B ^ 3 ≤ -(ρ * B ^ 3) := by
  have hmain : 6 * ρ * B ^ 3 ≤ (3 * θ / (8 * η)) * S := by
    calc
      _ = (3 / (8 * η) * B ^ 2) * (16 * ρ * B * η) := by field_simp; ring
      _ ≤ (3 / (8 * η) * B ^ 2) * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (3 * θ / (8 * η)) * (θ * B ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)
  have hs : 16 * ρ * B * η * K ≤ θ := by
    calc
      _ ≤ θ ^ 2 * K := mul_le_mul_of_nonneg_right hscale hK
      _ = θ * (θ * K) := by ring
      _ ≤ θ * 1 := mul_le_mul_of_nonneg_left hlength hθ.le
      _ = θ := mul_one _
  have herr : 8 * η * ρ ^ 2 * B ^ 4 * K / θ ≤ ρ * B ^ 3 / 2 := by
    rw [div_le_iff₀ hθ]
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ ρ * B ^ 3 / 2 by positivity)
    nlinarith only [hh]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] {f : E → ℝ} (start : E)

/-- Every completed restart of the genuine accelerated method decreases
the function by at least `ρ B³`. Both last-gradient cases are proved. -/
theorem restarted_epoch_decrease (hf : ContDiff ℝ 2 f) {L : ℝ}
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hη : 0 < η) (hstep : L * η ≤ 1 / 4) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hscale : 16 * ρ * B * η ≤ θ ^ 2) (n : ℕ)
    (hlength : θ * (n + 1 : ℕ) ≤ 1)
    (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2)
    (hrestart : B ^ 2 < (n + 1 : ℕ) * epochEnergy f η θ start (n + 1)) :
    f (epochPoint f η θ start (n + 1)) - f start ≤ -(ρ * B ^ 3) := by
  by_cases hsmall : η * ‖gradient f (epochQuery f η θ start n)‖ ≤ B
  · have hnorm0 : ‖fderiv ℝ (gradient f) start‖ ≤ L :=
      norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall (fun y => hlip y start))
    have hnorm : η * ‖fderiv ℝ (gradient f) start‖ ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left hnorm0 hη.le
      nlinarith
    have hs := small_gradient_epoch_decrease start hf hρ hB hH hη hnorm hθ hθ1 n hbudget hsmall
    have he : θ * B ^ 2 ≤ epochEnergy f η θ start (n + 1) := by
      have hr := mul_le_mul_of_nonneg_left hrestart.le hθ.le
      have hk := mul_le_mul_of_nonneg_right hlength (epochEnergy_nonneg f η θ start (n + 1))
      nlinarith
    exact hs.trans (restart_model_bound hρ hB hη hθ (by positivity) hlength he hscale)
  · have hs := large_gradient_epoch_decrease start (hf.differentiable (by norm_num))
      hlip hη hstep hθ.le hθ1 hB n hbudget (le_of_lt (lt_of_not_ge hsmall))
    have hdrop : ρ * B ^ 3 ≤ B ^ 2 / (4 * η) := by
      rw [le_div_iff₀ (by positivity : 0 < 4 * η)]
      have hθsq : θ ^ 2 ≤ 1 := by nlinarith
      have hmax : 16 * ρ * B * η ≤ 1 := hscale.trans hθsq
      have hb := mul_le_mul_of_nonneg_right hmax (sq_nonneg B)
      have hn : 0 ≤ ρ * B ^ 3 * η := by positivity
      nlinarith
    exact hs.trans (neg_le_neg hdrop)

end RandomizedFO2003.Accelerated
