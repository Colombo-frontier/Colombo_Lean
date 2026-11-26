import FreshGradientMinimax.JointLevel
import FreshGradientMinimax.EstimatorTransport
import FreshGradientMinimax.EstimatorCost

/-! The F.1 estimator as a jointly measurable kernel in reference and query,
with exact transport of moments and cost to the earlier fixed-query laws. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def jointRelativeEstimatorKernel (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) : Kernel (Joint dx dy) (Euclid dy) :=
  multilevelKernel (fun j => S.jointLevelKernel O (2 ^ j)
    (levelSteps ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (2 ^ j)) a ha)
    (estimatorCutoff ρ m e σ)

instance jointRelativeEstimatorKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    IsMarkovKernel (S.jointRelativeEstimatorKernel O ρ m e a ha) := by
  unfold jointRelativeEstimatorKernel
  infer_instance

theorem jointRelativeEstimatorKernel_apply (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (u : Euclid dx) (v : Euclid dy) :
    S.jointRelativeEstimatorKernel O ρ m e a ha (u, v) = S.relativeEstimatorKernel O ρ m e v (a v) u :=
  multilevelKernel_congr_at _ _ _ _ (fun _ => S.jointLevelKernel_apply O _ _ a ha u v) _

theorem jointRelativeEstimatorKernel_integrable (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (z : Joint dx dy) :
    Integrable id (S.jointRelativeEstimatorKernel O ρ m e a ha z) := by
  rcases z with ⟨u, v⟩
  rw [S.jointRelativeEstimatorKernel_apply]
  exact S.relativeEstimatorKernel_integrable O ρ m e v (a v) u

theorem jointRelativeEstimatorKernel_square_integrable (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (z : Joint dx dy) :
    Integrable (fun r => ‖r - (gradient S.effectiveValue z.2 + a z.2)‖ ^ 2)
      (S.jointRelativeEstimatorKernel O ρ m e a ha z) := by
  rcases z with ⟨u, v⟩
  rw [S.jointRelativeEstimatorKernel_apply]
  exact S.relativeEstimatorKernel_square_integrable O ρ m e v (a v) u

theorem jointRelativeEstimatorKernel_bias (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ}
    (hρ : 0 < ρ) (hm : 0 < m) (he : 0 < e)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (z : Joint dx dy) :
    ‖(∫ r, r ∂S.jointRelativeEstimatorKernel O ρ m e a ha z) -
      (gradient S.effectiveValue z.2 + a z.2)‖ ^ 2 ≤
      ρ * m * e + ρ * m ^ 2 * ‖z.1 - S.sliceMin z.2‖ ^ 2 := by
  rcases z with ⟨u, v⟩
  rw [S.jointRelativeEstimatorKernel_apply]
  exact S.relativeEstimatorKernel_bias O hαℓ hfast hρ hm he v (a v) u

theorem jointRelativeEstimatorKernel_variance (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ} (hρ : 0 < ρ) (hm : 0 < m)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (z : Joint dx dy) :
    (∫ r, ‖r - ∫ w, w ∂S.jointRelativeEstimatorKernel O ρ m e a ha z‖ ^ 2
      ∂S.jointRelativeEstimatorKernel O ρ m e a ha z) ≤
      140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2 + ρ * m ^ 2 * ‖z.1 - S.sliceMin z.2‖ ^ 2 := by
  rcases z with ⟨u, v⟩
  rw [S.jointRelativeEstimatorKernel_apply]
  exact S.relativeEstimatorKernel_variance O hαℓ hfast hρ hm v (a v) u

def jointCostedEstimatorKernel (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) : Kernel (Joint dx dy) (Euclid dy × ℕ) :=
  costedMultilevelKernel (fun j => S.jointLevelKernel O (2 ^ j)
    (levelSteps ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (2 ^ j)) a ha)
    (levelWork ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m) (estimatorCutoff ρ m e σ)

instance jointCostedEstimatorKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    IsMarkovKernel (S.jointCostedEstimatorKernel O ρ m e a ha) := by
  unfold jointCostedEstimatorKernel
  infer_instance

theorem jointCostedEstimatorKernel_apply (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (u : Euclid dx) (v : Euclid dy) :
    S.jointCostedEstimatorKernel O ρ m e a ha (u, v) = S.costedRelativeEstimatorKernel O ρ m e v (a v) u :=
  costedMultilevelKernel_congr_at _ _ _ _ (fun _ => S.jointLevelKernel_apply O _ _ a ha u v) _ _

theorem jointCostedEstimatorKernel_first (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    (S.jointCostedEstimatorKernel O ρ m e a ha).map Prod.fst = S.jointRelativeEstimatorKernel O ρ m e a ha :=
  costedMultilevelKernel_first _ _ _

theorem jointCostedEstimatorKernel_mean_cost (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (z : Joint dx dy) :
    (∫ r, (r.2 : ℝ) ∂S.jointCostedEstimatorKernel O ρ m e a ha z) =
      multilevelWork ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (estimatorCutoff ρ m e σ) :=
  costedMultilevelKernel_mean_cost _ _ _ _

end SCObjective
end FreshGradientMinimax
