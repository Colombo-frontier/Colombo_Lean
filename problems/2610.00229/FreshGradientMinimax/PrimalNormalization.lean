import FreshGradientMinimax.RecursiveInitialization

/-! Lowering the advertised primal strong-convexity constant preserves
the objective, oracle and actual saddle. This also covers a zero-dimensional
fast variable, where alpha need not be bounded by the smoothness constant. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

def weakenPrimal {β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) : SCObjective dx dy ℓ μ β where
  toNCObjective := S.toNCObjective
  α_pos := hβ
  primal_strong := by
    intro v u w
    have h := S.primal_strong v u w
    have hm := mul_le_mul_of_nonneg_right hβα (sq_nonneg ‖w - u‖)
    dsimp only at h ⊢
    linarith only [h, hm]

theorem weakenPrimal_objective {β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) :
    (S.weakenPrimal hβ hβα).toNCObjective = S.toNCObjective := rfl

theorem weakenPrimal_saddle {β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) :
    (S.weakenPrimal hβ hβα).saddleU = S.saddleU ∧ (S.weakenPrimal hβ hβα).saddleV = S.saddleV :=
  S.stationary_saddle_unique _ _ (S.weakenPrimal hβ hβα).saddle_gradX_zero
    (S.weakenPrimal hβ hβα).saddle_gradY_zero

theorem weakenPrimal_gap {β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) (u : Euclid dx) (v : Euclid dy) :
    (S.weakenPrimal hβ hβα).gap u v = S.gap u v := rfl

theorem weakenPrimal_startEnergy {β : ℝ} (hβ : 0 < β) (hβα : β ≤ α) :
    (S.weakenPrimal hβ hβα).saddleStartEnergy = S.saddleStartEnergy := by
  funext z
  simp only [saddleStartEnergy, (S.weakenPrimal_saddle hβ hβα).1, (S.weakenPrimal_saddle hβ hβα).2]

def normalizedPrimal : SCObjective dx dy ℓ μ (min α ℓ) :=
  S.weakenPrimal (lt_min S.α_pos S.L_pos) (min_le_left _ _)

include S in
theorem normalizedPrimal_fast (hfast : ℓ / 4 ≤ α) : ℓ / 4 ≤ min α ℓ :=
  le_min hfast (by have := S.L_pos; linarith)

theorem normalizedPrimal_startEnergy : S.normalizedPrimal.saddleStartEnergy = S.saddleStartEnergy :=
  S.weakenPrimal_startEnergy _ _

end SCObjective
end FreshGradientMinimax
