import RandomizedFO2003.EpochGradientAverage
import Mathlib.Data.Finset.Max

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ) (η θ : ℝ) (start : E)

theorem epochEnergy_mono {n N : ℕ} (hn : n ≤ N) :
    epochEnergy f η θ start n ≤ epochEnergy f η θ start N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ => sq_nonneg _)

theorem epoch_restart_budget_mono {n N : ℕ} (hn : n ≤ N) :
    (n : ℝ) * epochEnergy f η θ start n ≤ (N : ℝ) * epochEnergy f η θ start N :=
  mul_le_mul (by exact_mod_cast hn) (epochEnergy_mono f η θ start hn)
    (epochEnergy_nonneg f η θ start n) (by positivity)

/-- Any least step in the latter half of a non-restarted epoch is small.
The constant 2 avoids square roots and is sufficient for the sharp rate. -/
theorem epoch_half_min_step_le {B : ℝ} (hB : 0 ≤ B) {N q : ℕ} (hN : 0 < N)
    (hq0 : N / 2 ≤ q) (hqN : q < N)
    (hmin : ∀ k, N / 2 ≤ k → k < N →
      ‖epochIncrement f η θ start q‖ ≤ ‖epochIncrement f η θ start k‖)
    (hbudget : (N : ℝ) * epochEnergy f η θ start N ≤ B ^ 2) :
    ‖epochIncrement f η θ start q‖ ≤ 2 * B / N := by
  have hsum : ((N - N / 2 : ℕ) : ℝ) * ‖epochIncrement f η θ start q‖ ^ 2 ≤
      epochEnergy f η θ start N := by
    calc
      _ = ∑ _k ∈ Finset.Ico (N / 2) N, ‖epochIncrement f η θ start q‖ ^ 2 := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.Ico (N / 2) N, ‖epochIncrement f η θ start k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
          (hmin k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk => Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2) (fun _ _ _ => sq_nonneg _)
  have hcard : (N : ℝ) ≤ 2 * ((N - N / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ 2 * (N - N / 2) by omega)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hscaled := (mul_le_mul_of_nonneg_left hsum hNreal.le).trans hbudget
  have hcardScaled := mul_le_mul_of_nonneg_right hcard
    (mul_nonneg hNreal.le (sq_nonneg ‖epochIncrement f η θ start q‖))
  rw [le_div_iff₀ hNreal]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith [sq_nonneg B]

theorem exists_epoch_half_min {N : ℕ} (hN : 0 < N) :
    ∃ q, N / 2 ≤ q ∧ q < N ∧ ∀ k, N / 2 ≤ k → k < N →
      ‖epochIncrement f η θ start q‖ ≤ ‖epochIncrement f η θ start k‖ := by
  have hs : (Finset.Ico (N / 2) N).Nonempty :=
    Finset.nonempty_Ico.mpr (Nat.div_lt_self hN (by norm_num))
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (Finset.Ico (N / 2) N)
    (fun k => ‖epochIncrement f η θ start k‖) hs
  exact ⟨q, (Finset.mem_Ico.mp hq).1, (Finset.mem_Ico.mp hq).2,
    fun k hk0 hkN => hmin k (Finset.mem_Ico.mpr ⟨hk0, hkN⟩)⟩

variable {f η θ}

/-- Terminal guarantee for the actual latter-half-minimum average. This
uses the original C² and Lipschitz-Hessian hypotheses and the actual
trajectory's restart test; no convergence premise is assumed. -/
theorem terminal_average_gradient_le (hf : ContDiff ℝ 2 f) {ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hη : 0 < η) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {N q : ℕ} (hN : 0 < N)
    (hq0 : N / 2 ≤ q) (hqN : q < N)
    (hmin : ∀ k, N / 2 ≤ k → k < N →
      ‖epochIncrement f η θ start q‖ ≤ ‖epochIncrement f η θ start k‖)
    (hbudget : (N : ℝ) * epochEnergy f η θ start N ≤ B ^ 2) :
    ‖gradient f (prefixAverage (epochQuery f η θ start) q)‖ ≤
      4 * B / (η * (N : ℝ) ^ 2) + 2 * θ * B / (η * N) + 4 * ρ * B ^ 2 := by
  have hpartial (k : ℕ) (hk : k ≤ N) : (k : ℝ) * epochEnergy f η θ start k ≤ B ^ 2 :=
    (epoch_restart_budget_mono f η θ start hk).trans hbudget
  have hy (k : ℕ) (hk : k < q + 1) : ‖epochQuery f η θ start k - start‖ ≤ 2 * B :=
    (epoch_geometry_of_restart_budget f η θ start hB hθ hθ1 k (hpartial k (by omega))).2.2
  have hx := (epoch_geometry_of_restart_budget f η θ start hB hθ hθ1 q (hpartial q hqN.le)).1
  have hv := epoch_half_min_step_le f η θ start hB hN hq0 hqN hmin hbudget
  have ha := epoch_average_gradient_bound start hf hρ (show 0 ≤ 2 * B by positivity) hH hη hθ q hy hx hv
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hmid : (N : ℝ) ≤ 2 * (q + 1) := by exact_mod_cast (show N ≤ 2 * (q + 1) by omega)
  have hc : (2 * B / N + θ * B) / (η * (q + 1)) ≤
      4 * B / (η * (N : ℝ) ^ 2) + 2 * θ * B / (η * N) := by
    calc
      _ ≤ (2 * B / N + θ * B) / (η * ((N : ℝ) / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (by linarith) hη.le)
      _ = _ := by field_simp; ring
  nlinarith

end RandomizedFO2003.Accelerated
