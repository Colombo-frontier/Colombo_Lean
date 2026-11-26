import FreshGradientMinimax.FastBatchMachine

/-! The fast-refresh tag is now the explicit horizon of an original-query
algorithm. Its full joint output is recovered from its actual transcript. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem refresh_original_history (O : FreshOracle S.toNCObjective σ) (m E : ℝ) :
    ((fastBatchAlgorithm dx dy ℓ (refreshBatch ℓ α σ m E)).historyKernel O.kernel
      (refreshSteps ℓ α * refreshBatch ℓ α σ m E)).map
      (fun h => ((fastBatchMachine (dx := dx) (dy := dy) ℓ (refreshBatch ℓ α σ m E)).replay
        batchInitial (refreshSteps ℓ α * refreshBatch ℓ α σ m E) h).1) = S.refreshKernel O m E :=
  S.fastBatchAlgorithm_joint_state O (refreshBatch_pos ℓ α σ m E) (refreshSteps ℓ α)

theorem refresh_original_law (O : FreshOracle S.toNCObjective σ) (m E : ℝ) (ν : Measure (Joint dx dy)) :
    (((fastBatchAlgorithm dx dy ℓ (refreshBatch ℓ α σ m E)).historyKernel O.kernel
      (refreshSteps ℓ α * refreshBatch ℓ α σ m E)) ∘ₘ ν).map
      (fun h => ((fastBatchMachine (dx := dx) (dy := dy) ℓ (refreshBatch ℓ α σ m E)).replay
        batchInitial (refreshSteps ℓ α * refreshBatch ℓ α σ m E) h).1) = S.refreshKernel O m E ∘ₘ ν := by
  rw [Measure.map_comp _ _ (f := fun h => ((fastBatchMachine (dx := dx) (dy := dy) ℓ (refreshBatch ℓ α σ m E)).replay
    batchInitial (refreshSteps ℓ α * refreshBatch ℓ α σ m E) h).1)
    (measurable_fst.comp ((fastBatchMachine ℓ (refreshBatch ℓ α σ m E)).replay_measurable
    batchInitial batchInitial_measurable _)), S.refresh_original_history]

theorem refresh_original_tagged_kernel (O : FreshOracle S.toNCObjective σ) (m E : ℝ) :
    ((fastBatchAlgorithm dx dy ℓ (refreshBatch ℓ α σ m E)).historyKernel O.kernel
      (refreshSteps ℓ α * refreshBatch ℓ α σ m E)).map
      (fun h => (((fastBatchMachine (dx := dx) (dy := dy) ℓ (refreshBatch ℓ α σ m E)).replay
        batchInitial (refreshSteps ℓ α * refreshBatch ℓ α σ m E) h).1,
        refreshSteps ℓ α * refreshBatch ℓ α σ m E)) =
      taggedKernel (S.refreshKernel O m E) (refreshSteps ℓ α * refreshBatch ℓ α σ m E) := by
  rw [taggedKernel, ← S.refresh_original_history O m E,
    ← Kernel.map_comp_right _
      (f := fun h => ((fastBatchMachine (dx := dx) (dy := dy) ℓ (refreshBatch ℓ α σ m E)).replay
        batchInitial (refreshSteps ℓ α * refreshBatch ℓ α σ m E) h).1)
      (g := fun z : Joint dx dy => (z, refreshSteps ℓ α * refreshBatch ℓ α σ m E))
      (measurable_fst.comp ((fastBatchMachine ℓ (refreshBatch ℓ α σ m E)).replay_measurable
        batchInitial batchInitial_measurable _))
      (measurable_id.prodMk measurable_const)]
  rfl

theorem refresh_original_accuracy (O : FreshOracle S.toNCObjective σ) (hαℓ : α ≤ ℓ)
    {m E : ℝ} (hm : 0 < m) (hE : 0 < E) (u : Euclid dx) (v : Euclid dy) :
    Integrable (fun w => m * ‖w - S.sliceMin v‖ ^ 2)
      ((fastBatchMethod dx dy ℓ (refreshBatch ℓ α σ m E) u v).outputLaw O.kernel
        (refreshSteps ℓ α * refreshBatch ℓ α σ m E)) ∧
    (∫ w, m * ‖w - S.sliceMin v‖ ^ 2
      ∂(fastBatchMethod dx dy ℓ (refreshBatch ℓ α σ m E) u v).outputLaw O.kernel
        (refreshSteps ℓ α * refreshBatch ℓ α σ m E)) ≤
      S.fastError m (u, v) / 1000000 + E / 1000000 := by
  rw [S.fastBatchMethod_law O (refreshBatch_pos ℓ α σ m E)]
  refine ⟨(S.fastRunKernel_square_integrable O (refreshBatch_pos ℓ α σ m E) v (refreshSteps ℓ α) u).const_mul m, ?_⟩
  have h := S.refreshKernel_fast_bound O hαℓ hm hE (u, v)
  rw [S.refreshKernel_apply, integral_map (f := S.fastError m) (φ := fun w : Euclid dx => (w, v))
    (measurable_id.prodMk measurable_const).aemeasurable (S.fastError_continuous m).aestronglyMeasurable] at h
  exact h

end SCObjective
end FreshGradientMinimax
