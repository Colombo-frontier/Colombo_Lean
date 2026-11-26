import FreshGradientMinimax.JointEpoch

/-! The explicit fast-variable refresh parameters in F.3. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax

def refreshSteps (ℓ α : ℝ) : ℕ := ⌈(ℓ / α) * Real.log 1000000⌉₊

def refreshBatch (ℓ α σ m E : ℝ) : ℕ := max 1 ⌈1000000 * σ ^ 2 * m / (α * ℓ * E)⌉₊

theorem refreshBatch_pos (ℓ α σ m E : ℝ) : 0 < refreshBatch ℓ α σ m E :=
  lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)

theorem refreshSteps_contraction {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (hαℓ : α ≤ ℓ) :
    (1 - α / ℓ) ^ refreshSteps ℓ α ≤ 1 / (1000000 : ℝ) := by
  have h := geometric_decay_log_ceiling (div_pos hα hℓ) ((div_le_one hℓ).mpr hαℓ)
    (by norm_num : (0 : ℝ) < 1000000)
  have he : Real.log 1000000 / (α / ℓ) = (ℓ / α) * Real.log 1000000 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he] at h
  exact h

theorem refreshBatch_noise {ℓ α σ m E : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (hE : 0 < E) :
    m * (σ ^ 2 / (α * ℓ * refreshBatch ℓ α σ m E)) ≤ E / 1000000 := by
  have hb : (0 : ℝ) < refreshBatch ℓ α σ m E := by exact_mod_cast refreshBatch_pos ℓ α σ m E
  have hc : 1000000 * σ ^ 2 * m / (α * ℓ * E) ≤ (refreshBatch ℓ α σ m E : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hs := (div_le_iff₀ (mul_pos (mul_pos hα hℓ) hE)).mp hc
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos (mul_pos hα hℓ) hb) (by norm_num)).mpr
  nlinarith only [hs]

end FreshGradientMinimax
