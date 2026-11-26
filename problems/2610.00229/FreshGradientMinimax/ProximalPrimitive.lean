import FreshGradientMinimax.ProximalRandomAccuracy

/-! Accuracy and the original-call rate for the same random-center
proximal program. Halving its internal tolerance changes only a universal
constant, leaving the eighth logarithmic power unchanged. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

theorem valueLogFactor_half {ℓ σ μ η : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ) (hη : 0 < η) :
    valueLogFactor ℓ σ μ (η / 2) ≤ 2 * valueLogFactor ℓ σ μ η := by
  have hn : σ ^ 2 / (μ * (η / 2)) = 2 * (σ ^ 2 / (μ * η)) := by ring
  have hs := log_scaled_add_two (by norm_num : (1 : ℝ) ≤ 2)
    (by positivity : 0 ≤ σ ^ 2 / (μ * η))
  have hL := (valueLogFactor_bounds (σ := σ) hℓ hμ hη).1
  unfold valueLogFactor at hL ⊢
  rw [hn]
  linarith [log_two_bounds.2]

theorem initialization_log_half {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) :
    Real.log (2 + x / (η / 2)) ≤ 3 * Real.log (2 + x / η) := by
  have hxη : 0 ≤ x / η := div_nonneg hx hη.le
  have hs := log_scaled_add_two (by norm_num : (1 : ℝ) ≤ 2) hxη
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ 2 + x / η by linarith)
  rw [show x / (η / 2) = 2 * (x / η) by ring]
  linarith [log_two_bounds.1, log_two_bounds.2]

theorem scscSolverWork_half_rate {ℓ α σ μ η E₀ : ℝ}
    (hμ : 0 < μ) (hμℓ : μ ≤ ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hη : 0 < η) (hE : 0 ≤ E₀) :
    scscSolverWork ℓ α σ μ (η / 2) E₀ ≤ 10 ^ 114 * valueLogFactor ℓ σ μ η ^ 8 *
      (Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  have hℓ := hμ.trans_le hμℓ
  let Λ := valueLogFactor ℓ σ μ η
  let D := Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η)
  let N := σ ^ 2 / (μ * η)
  have hΛ : 0 ≤ Λ := le_trans (by norm_num) (valueLogFactor_bounds hℓ hμ hη).1
  have hΛhalf : 0 ≤ valueLogFactor ℓ σ μ (η / 2) :=
    le_trans (by norm_num) (valueLogFactor_bounds hℓ hμ (half_pos hη)).1
  have hD : 0 ≤ D := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply Real.log_nonneg
    have hx : 0 ≤ (ℓ / μ) * E₀ / η := by positivity
    linarith
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : valueLogFactor ℓ σ μ (η / 2) ^ 8 ≤ 256 * Λ ^ 8 := by
    have h := pow_le_pow_left₀ hΛhalf (valueLogFactor_half hℓ hμ hη) 8
    norm_num only [mul_pow] at h
    exact h
  have hinner : Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / (η / 2)) +
      σ ^ 2 / (μ * (η / 2)) ≤ 3 * (D + N) := by
    have hd := mul_le_mul_of_nonneg_left
      (initialization_log_half (show 0 ≤ (ℓ / μ) * E₀ by positivity) hη) (Real.sqrt_nonneg (ℓ / μ))
    rw [show σ ^ 2 / (μ * (η / 2)) = 2 * N by dsimp [N]; ring]
    dsimp only [D] at *
    nlinarith only [hd, hN]
  calc
    _ ≤ 10 ^ 110 * valueLogFactor ℓ σ μ (η / 2) ^ 8 *
        (Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / (η / 2)) + σ ^ 2 / (μ * (η / 2))) :=
      scscSolverWork_rate hμ hμℓ hα hfast (half_pos hη) hE
    _ ≤ 10 ^ 110 * valueLogFactor ℓ σ μ (η / 2) ^ 8 * (3 * (D + N)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ 10 ^ 110 * (256 * Λ ^ 8) * (3 * (D + N)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)
    _ = (768 * 10 ^ 110) * Λ ^ 8 * (D + N) := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (by norm_num : (768 * 10 ^ 110 : ℝ) ≤ 10 ^ 114)
        (show 0 ≤ Λ ^ 8 * (D + N) by positivity)
      simpa only [mul_assoc] using h

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem proximalSolverProgram_accuracy_cost (O : FreshOracle F σ) {η E₀ : ℝ}
    (hη : 0 < η) (hE : 0 < E₀) (ν : Measure (Euclid dx × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable F.proximalStartEnergy ν) (hb : (∫ p, F.proximalStartEnergy p ∂ν) ≤ E₀) :
    Integrable (fun t : (Euclid dx × Joint dx dy) × ℕ => F.proximalGap t.1)
      ((proximalSolverProgram dx dy L σ μ (η / 2) E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, F.proximalGap t.1 ∂(proximalSolverProgram dx dy L σ μ (η / 2) E₀).originalKernel O.kernel ∘ₘ ν) ≤ η ∧
    Integrable costValue ((proximalSolverProgram dx dy L σ μ (η / 2) E₀).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(proximalSolverProgram dx dy L σ μ (η / 2) E₀).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 114 * valueLogFactor (3 * L) σ μ η ^ 8 *
        (Real.sqrt ((3 * L) / μ) * Real.log (2 + ((3 * L) / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  have ha := F.proximalSolverProgram_random_accuracy O hη hE ν hi hb
  have hc := F.proximalSolverProgram_random_cost O (η / 2) E₀ ν
  refine ⟨ha.1, ha.2, hc.1, ?_⟩
  rw [hc.2]
  have hL := F.L_pos
  exact scscSolverWork_half_rate F.μ_pos (by have := F.μ_le_L; linarith)
    hL (by linarith) hη hE.le

end NCObjective
end FreshGradientMinimax
