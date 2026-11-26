import FreshGradientMinimax.JointEstimator

/-! Fresh averaging of the actual multilevel estimator used at each F.3 query. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def jointBatchedEstimatorKernel (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (b : ℕ) : Kernel (Joint dx dy) (Euclid dy) :=
  batchKernel (S.jointRelativeEstimatorKernel O ρ m e a ha) b

instance jointBatchedEstimatorKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (b : ℕ) :
    IsMarkovKernel (S.jointBatchedEstimatorKernel O ρ m e a ha b) := by
  unfold jointBatchedEstimatorKernel
  infer_instance

theorem jointBatchedEstimator_contract (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ}
    (hρ : 0 < ρ) (hm : 0 < m) (he : 0 < e)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) {b : ℕ} (hb : 0 < b) (z : Joint dx dy) :
    Integrable id (S.jointBatchedEstimatorKernel O ρ m e a ha b z) ∧
    Integrable (fun r => ‖r - (gradient S.effectiveValue z.2 + a z.2)‖ ^ 2)
      (S.jointBatchedEstimatorKernel O ρ m e a ha b z) ∧
    ‖(∫ r, r ∂S.jointBatchedEstimatorKernel O ρ m e a ha b z) -
      (gradient S.effectiveValue z.2 + a z.2)‖ ^ 2 ≤
      ρ * m * e + ρ * m ^ 2 * ‖z.1 - S.sliceMin z.2‖ ^ 2 ∧
    (∫ r, ‖r - ∫ w, w ∂S.jointBatchedEstimatorKernel O ρ m e a ha b z‖ ^ 2
      ∂S.jointBatchedEstimatorKernel O ρ m e a ha b z) ≤
      (140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2 + ρ * m ^ 2 * ‖z.1 - S.sliceMin z.2‖ ^ 2) / b := by
  let M := S.jointRelativeEstimatorKernel O ρ m e a ha
  let q := ∫ r, r ∂M z
  have hi := S.jointRelativeEstimatorKernel_integrable O ρ m e a ha z
  have ht := S.jointRelativeEstimatorKernel_square_integrable O ρ m e a ha z
  have hs := square_integrable_of_centered hi (gradient S.effectiveValue z.2 + a z.2) ht
  have hc : Integrable (fun r => ‖r - q‖ ^ 2) (M z) := integrable_square_sub_const hi hs q
  obtain ⟨hbi, hbm, hbs, hbv⟩ := batchKernel_moments M z q hi rfl hc hb
  have htarget : Integrable (fun r => ‖r - (gradient S.effectiveValue z.2 + a z.2)‖ ^ 2)
      (batchKernel M b z) := integrable_square_sub_const hbi
        (square_integrable_of_centered hbi q hbs) _
  refine ⟨hbi, htarget, ?_, ?_⟩
  · change ‖(∫ r, r ∂batchKernel M b z) - _‖ ^ 2 ≤ _
    rw [hbm]
    exact S.jointRelativeEstimatorKernel_bias O hαℓ hfast hρ hm he a ha z
  · change (∫ r, ‖r - ∫ w, w ∂batchKernel M b z‖ ^ 2 ∂batchKernel M b z) ≤ _
    rw [hbm, hbv]
    exact div_le_div_of_nonneg_right
      (S.jointRelativeEstimatorKernel_variance O hαℓ hfast hρ hm a ha z) (Nat.cast_nonneg b)

end SCObjective
end FreshGradientMinimax
