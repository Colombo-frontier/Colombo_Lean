import RandomizedFO2003.EpochParameters

namespace RandomizedFO2003.Accelerated

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {ε L ρ : ℝ} (start : E)

local notation "η₀" => stepSize L
local notation "B₀" => accuracyRadius ε ρ
local notation "N₀" => epochHorizon η₀ ρ B₀
local notation "θ₀" => roundedMomentum η₀ ρ B₀

/-- The rounded, explicitly configured epoch produces the requested
accuracy, including the constants lost to averaging and integer rounding. -/
theorem accuracy_epoch_terminal (hf : ContDiff ℝ 2 f)
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    {q : ℕ} (hq0 : N₀ / 2 ≤ q) (hqN : q < N₀)
    (hmin : ∀ k, N₀ / 2 ≤ k → k < N₀ →
      ‖epochIncrement f η₀ θ₀ start q‖ ≤ ‖epochIncrement f η₀ θ₀ start k‖)
    (hbudget : (N₀ : ℝ) * epochEnergy f η₀ θ₀ start N₀ ≤ B₀ ^ 2) :
    ‖gradient f (prefixAverage (epochQuery f η₀ θ₀ start) q)‖ ≤ ε := by
  have hB := accuracyRadius_pos hε hρ
  have hη := stepSize_pos hL
  have hraw := accuracy_rawMomentum_small hε hL hρ haccuracy
  have hp := roundedMomentum_conditions hη hρ hB hraw
  have ht := terminal_average_gradient_le start hf hρ.le hB.le hH hη hp.2.1.le hp.2.2.1
    hp.1 hq0 hqN hmin hbudget
  have hb := rounded_terminal_bound hη hρ hB hraw
  have hs := accuracyRadius_sq hε.le hρ
  have he : 388 * ρ * B₀ ^ 2 ≤ ε := by nlinarith
  exact ht.trans (hb.trans he)

variable [FiniteDimensional ℝ E]

/-- The same explicit settings also give the uniform decrease needed to
count every restart, without a hypothesis about a minimizer. -/
theorem accuracy_epoch_restart (hf : ContDiff ℝ 2 f)
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (n : ℕ) (hlength : n + 1 ≤ N₀)
    (hbudget : (n : ℝ) * epochEnergy f η₀ θ₀ start n ≤ B₀ ^ 2)
    (hrestart : B₀ ^ 2 < (n + 1 : ℕ) * epochEnergy f η₀ θ₀ start (n + 1)) :
    f (epochPoint f η₀ θ₀ start (n + 1)) - f start ≤ -(ρ * B₀ ^ 3) := by
  have hB := accuracyRadius_pos hε hρ
  have hη := stepSize_pos hL
  have hraw := accuracy_rawMomentum_small hε hL hρ haccuracy
  have hp := roundedMomentum_conditions hη hρ hB hraw
  have hk : θ₀ * (n + 1 : ℕ) ≤ 1 := by
    calc
      _ ≤ θ₀ * (N₀ : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hlength) hp.2.1.le
      _ = 1 := hp.2.2.2.1
  exact restarted_epoch_decrease start hf hL.le hρ.le hB.le hlip hH hη
    (stepSize_mul hL).le hp.2.1 hp.2.2.1 hp.2.2.2.2.1 n hk hbudget hrestart

end RandomizedFO2003.Accelerated
