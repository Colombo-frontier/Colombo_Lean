import FreshGradientMinimax.CostedComposition
import FreshGradientMinimax.FullEpoch

/-! The full epoch with all sampled estimator costs retained. The first
marginal equals the previously analysed epoch, and its exact mean cost is
independent of the input state. EpochProgram proves the original-query
transcript implementation of this joint law. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def estimatorWork (ℓ α ρ m e σ : ℝ) : ℝ :=
  multilevelWork ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (estimatorCutoff ρ m e σ)

def fullEpochWork (ℓ α σ m H e E : ℝ) : ℝ :=
  (epochSteps m H : ℝ) * (epochBatch m H e σ E : ℝ) * estimatorWork ℓ α epochRho m e σ +
    (refreshSteps ℓ α : ℝ) * (refreshBatch ℓ α σ m E : ℝ)

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def costedJointBatchedKernel (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) : Kernel (Joint dx dy) (Euclid dy × ℕ) :=
  costedBatchKernel (S.jointCostedEstimatorKernel O ρ m e r hr) b

instance costedJointBatchedKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    IsMarkovKernel (S.costedJointBatchedKernel O ρ m e r hr b) := by
  unfold costedJointBatchedKernel
  infer_instance

theorem costedJointBatchedKernel_first (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    (S.costedJointBatchedKernel O ρ m e r hr b).map Prod.fst = S.jointBatchedEstimatorKernel O ρ m e r hr b := by
  rw [costedJointBatchedKernel, costedBatchKernel_first, S.jointCostedEstimatorKernel_first]
  rfl

theorem costedJointBatchedKernel_cost (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (z : Joint dx dy) :
    Integrable costValue (S.costedJointBatchedKernel O ρ m e r hr b z) ∧
    (∫ t, costValue t ∂S.costedJointBatchedKernel O ρ m e r hr b z) = (b : ℝ) * estimatorWork ℓ α ρ m e σ := by
  have hi : Integrable costValue (S.jointCostedEstimatorKernel O ρ m e r hr z) :=
    costedMultilevelKernel_cost_integrable _ _ _ _
  have h := costedBatchKernel_cost (S.jointCostedEstimatorKernel O ρ m e r hr) z hi b
  rw [show (∫ t, costValue t ∂S.jointCostedEstimatorKernel O ρ m e r hr z) = estimatorWork ℓ α ρ m e σ
    from S.jointCostedEstimatorKernel_mean_cost O ρ m e r hr z] at h
  exact h

def costedJointEpochStepKernel (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    Kernel (EpochState dx dy) (EpochState dx dy × ℕ) :=
  costedUpdateKernel ((S.costedJointBatchedKernel O ρ m e r hr b).comap
    (fun z : EpochState dx dy => (z.1, accelerationQuery (Real.sqrt (m / H)) z.2))
    (measurable_fst.prodMk ((accelerationQuery_continuous _).measurable.comp measurable_snd)))
    (referenceAccelerationUpdate (Real.sqrt (m / H)) m H) (fun _ => 0)

instance costedJointEpochStepKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    IsMarkovKernel (S.costedJointEpochStepKernel O ρ m H e r hr b) :=
  costedUpdateKernel_markov _ _ (referenceAccelerationUpdate_continuous _ _ _).measurable _ measurable_const

theorem costedJointEpochStepKernel_first (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    (S.costedJointEpochStepKernel O ρ m H e r hr b).map Prod.fst = S.jointEpochStepKernel O ρ m H e r hr b := by
  rw [costedJointEpochStepKernel, costedUpdateKernel_first _ _
    (referenceAccelerationUpdate_continuous _ _ _).measurable _ measurable_const,
    ← Kernel.comap_map_comm _ _ measurable_fst, S.costedJointBatchedKernel_first]
  rfl

theorem costedJointEpochStepKernel_cost (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (z : EpochState dx dy) :
    Integrable costValue (S.costedJointEpochStepKernel O ρ m H e r hr b z) ∧
    (∫ t, costValue t ∂S.costedJointEpochStepKernel O ρ m H e r hr b z) = (b : ℝ) * estimatorWork ℓ α ρ m e σ := by
  have h := S.costedJointBatchedKernel_cost O ρ m e r hr b (z.1, accelerationQuery (Real.sqrt (m / H)) z.2)
  have ht := costedUpdateKernel_cost ((S.costedJointBatchedKernel O ρ m e r hr b).comap
    (fun z : EpochState dx dy => (z.1, accelerationQuery (Real.sqrt (m / H)) z.2))
    (measurable_fst.prodMk ((accelerationQuery_continuous _).measurable.comp measurable_snd)))
    (referenceAccelerationUpdate (Real.sqrt (m / H)) m H)
    (referenceAccelerationUpdate_continuous _ _ _).measurable
    (fun _ : EpochState dx dy => 0) measurable_const z h.1
  simpa only [Kernel.comap_apply, Nat.cast_zero, zero_add, h.2] using ht

def costedEpochPhaseKernel (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : Kernel (Joint dx dy) (EpochState dx dy × ℕ) :=
  (costedIterate (S.costedJointEpochStepKernel O epochRho m H e r hr (epochBatch m H e σ E))
    (epochSteps m H)).comap (fun z : Joint dx dy => (z.1, (z.2, z.2)))
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))

instance costedEpochPhaseKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    IsMarkovKernel (S.costedEpochPhaseKernel O m H e E r hr) := by
  unfold costedEpochPhaseKernel
  infer_instance

theorem costedEpochPhaseKernel_first (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (S.costedEpochPhaseKernel O m H e E r hr).map Prod.fst = S.epochPhaseStateKernel O m H e E r hr := by
  rw [costedEpochPhaseKernel, ← Kernel.comap_map_comm _ _ measurable_fst, costedIterate_first,
    S.costedJointEpochStepKernel_first]
  rfl

theorem costedEpochPhaseKernel_cost (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (z : Joint dx dy) :
    Integrable costValue (S.costedEpochPhaseKernel O m H e E r hr z) ∧
    (∫ t, costValue t ∂S.costedEpochPhaseKernel O m H e E r hr z) =
      (epochSteps m H : ℝ) * (epochBatch m H e σ E : ℝ) * estimatorWork ℓ α epochRho m e σ := by
  have h := costedIterate_cost (S.costedJointEpochStepKernel O epochRho m H e r hr (epochBatch m H e σ E))
    (fun z => (S.costedJointEpochStepKernel_cost O epochRho m H e r hr _ z).1) _
    (fun z => (S.costedJointEpochStepKernel_cost O epochRho m H e r hr _ z).2) (epochSteps m H) (z.1, (z.2, z.2))
  simpa only [mul_assoc] using h

def costedFullEpochKernel (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : Kernel (Joint dx dy) (Joint dx dy × ℕ) :=
  costedCompose (S.costedEpochPhaseKernel O m H e E r hr)
    (taggedKernel (S.refreshFromStateKernel O m E) (refreshSteps ℓ α * refreshBatch ℓ α σ m E))

instance costedFullEpochKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    IsMarkovKernel (S.costedFullEpochKernel O m H e E r hr) := by
  unfold costedFullEpochKernel
  infer_instance

theorem costedFullEpochKernel_first (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (S.costedFullEpochKernel O m H e E r hr).map Prod.fst = S.fullEpochKernel O m H e E r hr := by
  rw [costedFullEpochKernel, costedCompose_first, taggedKernel_first, S.costedEpochPhaseKernel_first]
  rfl

theorem costedFullEpochKernel_cost (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (z : Joint dx dy) :
    Integrable costValue (S.costedFullEpochKernel O m H e E r hr z) ∧
    (∫ t, costValue t ∂S.costedFullEpochKernel O m H e E r hr z) = fullEpochWork ℓ α σ m H e E := by
  have hp := S.costedEpochPhaseKernel_cost O m H e E r hr z
  have h := costedCompose_cost (S.costedEpochPhaseKernel O m H e E r hr)
    (taggedKernel (S.refreshFromStateKernel O m E) (refreshSteps ℓ α * refreshBatch ℓ α σ m E)) z hp.1
    (fun t => taggedKernel_cost_integrable _ _ t) _ (fun t => taggedKernel_mean_cost _ _ t)
  simpa only [hp.2, Nat.cast_mul] using h

end SCObjective
end FreshGradientMinimax
