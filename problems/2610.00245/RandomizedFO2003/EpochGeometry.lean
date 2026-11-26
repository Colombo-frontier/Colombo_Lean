import RandomizedFO2003.AcceleratedEpoch

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
theorem norm_sum_sq_le_card_sum_sq {ι : Type*} (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have hnorm := norm_sum_le s v
  have hsum : 0 ≤ ∑ i ∈ s, ‖v i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hsum).mpr hnorm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simpa using hsq.trans (by simpa using hcs)

variable (f : E → ℝ) (η θ : ℝ) (start : E)

theorem epochPoint_displacement_sq (n : ℕ) :
    ‖epochPoint f η θ start n - start‖ ^ 2 ≤ (n : ℝ) * epochEnergy f η θ start n := by
  rw [← sum_epochIncrement]
  exact (norm_sum_sq_le_card_sum_sq (Finset.range n) (epochIncrement f η θ start)).trans_eq
    (by simp only [Finset.card_range, epochEnergy])

theorem epochMomentum_sq_le_energy (n : ℕ) :
    ‖epochMomentum f η θ start n‖ ^ 2 ≤ epochEnergy f η θ start n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [epochMomentum_succ, epochEnergy_succ]
    linarith [epochEnergy_nonneg f η θ start n]

theorem epochEnergy_le_of_restart_budget {B : ℝ} (n : ℕ)
    (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2) :
    epochEnergy f η θ start n ≤ B ^ 2 := by
  by_cases hn : n = 0
  · simp only [hn, epochEnergy_zero]
    exact sq_nonneg B
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    nlinarith [epochEnergy_nonneg f η θ start n]

theorem epoch_geometry_of_restart_budget {B : ℝ} (hB : 0 ≤ B)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ)
    (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2) :
    ‖epochPoint f η θ start n - start‖ ≤ B ∧
      ‖epochMomentum f η θ start n‖ ≤ B ∧ ‖epochQuery f η θ start n - start‖ ≤ 2 * B := by
  have hx : ‖epochPoint f η θ start n - start‖ ≤ B :=
    (sq_le_sq₀ (norm_nonneg _) hB).mp ((epochPoint_displacement_sq f η θ start n).trans hbudget)
  have hv : ‖epochMomentum f η θ start n‖ ≤ B :=
    (sq_le_sq₀ (norm_nonneg _) hB).mp ((epochMomentum_sq_le_energy f η θ start n).trans
      (epochEnergy_le_of_restart_budget f η θ start n hbudget))
  refine ⟨hx, hv, ?_⟩
  have hy : epochQuery f η θ start n - start = (epochPoint f η θ start n - start) +
      (1 - θ) • epochMomentum f η θ start n := by
    unfold epochQuery epochPoint epochMomentum extrapolate
    simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  rw [hy]
  have hn := norm_add_le (epochPoint f η θ start n - start) ((1 - θ) • epochMomentum f η θ start n)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ1)] at hn
  nlinarith [norm_nonneg (epochMomentum f η θ start n)]

theorem epoch_terminal_radius_of_small_gradient {B : ℝ} (hB : 0 ≤ B)
    (hη : 0 ≤ η) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ)
    (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2)
    (hsmall : η * ‖gradient f (epochQuery f η θ start n)‖ ≤ B) :
    ‖epochPoint f η θ start (n + 1) - start‖ ≤ 3 * B := by
  have hy := (epoch_geometry_of_restart_budget f η θ start hB hθ hθ1 n hbudget).2.2
  rw [epochPoint_succ, gradientStep]
  have he : epochQuery f η θ start n - η • gradient f (epochQuery f η θ start n) - start =
      (epochQuery f η θ start n - start) - η • gradient f (epochQuery f η θ start n) := by abel
  rw [he]
  have hn := norm_sub_le (epochQuery f η θ start n - start) (η • gradient f (epochQuery f η θ start n))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hn
  linarith

end RandomizedFO2003.Accelerated
