import FreshGradientMinimax.LevelMachine

/-! Equation (45) and its moments for the actual original-call transcript,
including the exact dyadic query horizon used by the work calculation. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem originalLevelKernel_apply (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (u : Euclid dx) (v : Euclid dy) :
    originalLevelKernel ℓ b n a O.kernel (u, v) = S.levelKernel O b n v (a v) u := by
  rw [S.originalLevelKernel_eq O hb n a ha, S.jointLevelKernel_apply]

theorem originalLevelKernel_integrable (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    Integrable id (originalLevelKernel ℓ b n a O.kernel q) ∧
    Integrable (fun r => ‖r - (gradient S.effectiveValue q.2 + a q.2)‖ ^ 2)
      (originalLevelKernel ℓ b n a O.kernel q) := by
  rcases q with ⟨u, v⟩
  rw [S.originalLevelKernel_apply O hb n a ha]
  exact ⟨S.levelKernel_integrable O hb n v (a v) u, S.levelKernel_square_integrable O hb n v (a v) u⟩

theorem originalLevelKernel_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {γ m : ℝ} (hγ : 0 < γ) (hm : 0 < m)
    {b : ℕ} (hb : 0 < b) (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    (∫ r, ‖r - (gradient S.effectiveValue q.2 + a q.2)‖ ^ 2
      ∂originalLevelKernel ℓ b (levelSteps ℓ α γ m b) a O.kernel q) ≤
        (γ * m ^ 2 * ‖q.1 - S.sliceMin q.2‖ ^ 2 + 10 * σ ^ 2) / b := by
  rcases q with ⟨u, v⟩
  rw [S.originalLevelKernel_apply O hb _ a ha]
  exact S.selected_level_accuracy O hαℓ hfast hγ hm hb v (a v) u

theorem originalLevelKernel_dyadic_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {γ m : ℝ} (hγ : 0 < γ) (hm : 0 < m)
    (j : ℕ) (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    (∫ r, ‖r - (gradient S.effectiveValue q.2 + a q.2)‖ ^ 2
      ∂originalLevelKernel ℓ (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a O.kernel q) ≤
        (1 / 2 : ℝ) ^ j * (γ * m ^ 2 * ‖q.1 - S.sliceMin q.2‖ ^ 2 + 10 * σ ^ 2) := by
  rcases q with ⟨u, v⟩
  rw [S.originalLevelKernel_apply O (pow_pos (by norm_num) j) _ a ha]
  exact S.dyadic_level_accuracy O hαℓ hfast hγ hm j v (a v) u

theorem dyadic_level_original_tagged_kernel (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) (j : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((levelAlgorithm dx dy ℓ (2 ^ j) (levelSteps ℓ α γ m (2 ^ j))).historyKernel O.kernel
      (levelWork ℓ α γ m j)).map (fun h =>
        (levelTranscriptRead ℓ (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a h, levelWork ℓ α γ m j)) =
      taggedKernel (S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha)
        (levelWork ℓ α γ m j) :=
  S.level_original_tagged_kernel O (pow_pos (by norm_num) j) _ a ha

end SCObjective
end FreshGradientMinimax
