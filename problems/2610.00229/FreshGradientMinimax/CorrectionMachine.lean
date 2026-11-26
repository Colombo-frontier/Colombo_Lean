import FreshGradientMinimax.LevelImplementation
import FreshGradientMinimax.IndependentMachines

/-! Three independently sampled levels implemented sequentially using
only fresh original oracle calls. The initial query is copied before
running any level, and each level retains its own state. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ}

abbrev CorrectionMachineState (dx dy : ℕ) :=
  LevelMachineState dx dy × (LevelMachineState dx dy × LevelMachineState dx dy)

def dyadicLevelMachine (dx dy : ℕ) (ℓ α γ m : ℝ) (j : ℕ) :=
  levelMachine dx dy ℓ (2 ^ j) (levelSteps ℓ α γ m (2 ^ j))

def correctionHorizon (ℓ α γ m : ℝ) (j : ℕ) : ℕ :=
  levelWork ℓ α γ m 0 + (levelWork ℓ α γ m (j + 1) + levelWork ℓ α γ m j)

def correctionMachine (dx dy : ℕ) (ℓ α γ m : ℝ) (j : ℕ) :
    OracleMachine dx dy (CorrectionMachineState dx dy) :=
  (dyadicLevelMachine dx dy ℓ α γ m 0).independentPair
    ((dyadicLevelMachine dx dy ℓ α γ m (j + 1)).independentPair
      (dyadicLevelMachine dx dy ℓ α γ m j) (levelWork ℓ α γ m (j + 1)))
    (levelWork ℓ α γ m 0)

def correctionInitial (q : Joint dx dy) : CorrectionMachineState dx dy :=
  (levelInitial q, (levelInitial q, levelInitial q))

theorem correctionInitial_measurable : Measurable (correctionInitial (dx := dx) (dy := dy)) :=
  levelInitial_measurable.prodMk (levelInitial_measurable.prodMk levelInitial_measurable)

def correctionRead (j : ℕ) (p : ℝ) (a : Euclid dy → Euclid dy)
    (s : CorrectionMachineState dx dy) : Euclid dy :=
  correctionValue p (levelRead (2 ^ 0) a s.1,
    (levelRead (2 ^ (j + 1)) a s.2.1, levelRead (2 ^ j) a s.2.2))

theorem correctionRead_measurable (j : ℕ) (p : ℝ) (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    Measurable (correctionRead (dx := dx) j p a) :=
  (correctionValue_continuous p).measurable.comp
    (((levelRead_measurable _ a ha).comp measurable_fst).prodMk
      (((levelRead_measurable _ a ha).comp measurable_snd.fst).prodMk
        ((levelRead_measurable _ a ha).comp measurable_snd.snd)))

def correctionAlgorithm (dx dy : ℕ) (ℓ α γ m : ℝ) (j : ℕ) : Algorithm dx dy (Joint dx dy) :=
  (correctionMachine dx dy ℓ α γ m j).compile correctionInitial correctionInitial_measurable

def correctionTranscriptRead (ℓ α γ m : ℝ) (j : ℕ) (p : ℝ) (a : Euclid dy → Euclid dy)
    (h : RunState dx dy (Joint dx dy) (correctionHorizon ℓ α γ m j)) : Euclid dy :=
  correctionRead j p a ((correctionMachine dx dy ℓ α γ m j).replay
    correctionInitial (correctionHorizon ℓ α γ m j) h)

theorem correctionTranscriptRead_measurable (ℓ α γ m : ℝ) (j : ℕ) (p : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    Measurable (correctionTranscriptRead (dx := dx) ℓ α γ m j p a) :=
  (correctionRead_measurable j p a ha).comp
    ((correctionMachine dx dy ℓ α γ m j).replay_measurable correctionInitial correctionInitial_measurable _)

theorem correctionMachine_run (ℓ α γ m : ℝ) (j : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (correctionMachine dx dy ℓ α γ m j).runKernel correctionInitial correctionInitial_measurable K
      (correctionHorizon ℓ α γ m j) =
    (dyadicLevelMachine dx dy ℓ α γ m 0).runKernel levelInitial levelInitial_measurable K (levelWork ℓ α γ m 0) ×ₖ
      ((dyadicLevelMachine dx dy ℓ α γ m (j + 1)).runKernel levelInitial levelInitial_measurable K
        (levelWork ℓ α γ m (j + 1)) ×ₖ
      (dyadicLevelMachine dx dy ℓ α γ m j).runKernel levelInitial levelInitial_measurable K (levelWork ℓ α γ m j)) := by
  unfold correctionMachine correctionHorizon correctionInitial
  rw [OracleMachine.independentPair_run, OracleMachine.independentPair_run]

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem correctionMachine_read (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) (j : ℕ) (p : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((correctionMachine dx dy ℓ α γ m j).runKernel correctionInitial correctionInitial_measurable O.kernel
      (correctionHorizon ℓ α γ m j)).map (correctionRead j p a) =
    independentCorrectionKernel
      (S.jointLevelKernel O (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a ha)
      (S.jointLevelKernel O (2 ^ (j + 1)) (levelSteps ℓ α γ m (2 ^ (j + 1))) a ha)
      (S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha) p := by
  rw [correctionMachine_run, independentCorrectionKernel,
    ← S.levelMachine_run O (pow_pos (by norm_num) 0) _ a ha,
    ← S.levelMachine_run O (pow_pos (by norm_num) (j + 1)) _ a ha,
    ← S.levelMachine_run O (pow_pos (by norm_num) j) _ a ha,
    Kernel.map_prod_map _ _ (levelRead_measurable (2 ^ (j + 1)) a ha) (levelRead_measurable (2 ^ j) a ha),
    Kernel.map_prod_map _ _ (levelRead_measurable (2 ^ 0) a ha)
      ((levelRead_measurable (2 ^ (j + 1)) a ha).prodMap (levelRead_measurable (2 ^ j) a ha)),
    ← Kernel.map_comp_right _
      ((levelRead_measurable (2 ^ 0) a ha).prodMap
        ((levelRead_measurable (2 ^ (j + 1)) a ha).prodMap (levelRead_measurable (2 ^ j) a ha)))
      (correctionValue_continuous p).measurable]
  rfl

theorem correction_original_history (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) (j : ℕ) (p : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((correctionAlgorithm dx dy ℓ α γ m j).historyKernel O.kernel (correctionHorizon ℓ α γ m j)).map
      (correctionTranscriptRead ℓ α γ m j p a) =
    independentCorrectionKernel
      (S.jointLevelKernel O (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a ha)
      (S.jointLevelKernel O (2 ^ (j + 1)) (levelSteps ℓ α γ m (2 ^ (j + 1))) a ha)
      (S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha) p := by
  rw [← S.correctionMachine_read O γ m j p a ha, OracleMachine.runKernel_eq_history,
    ← Kernel.map_comp_right _
      ((correctionMachine dx dy ℓ α γ m j).replay_measurable correctionInitial correctionInitial_measurable _)
      (correctionRead_measurable j p a ha)]
  rfl

theorem correction_original_tagged_kernel (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) (j : ℕ) (p : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((correctionAlgorithm dx dy ℓ α γ m j).historyKernel O.kernel (correctionHorizon ℓ α γ m j)).map
      (fun h => (correctionTranscriptRead ℓ α γ m j p a h, correctionHorizon ℓ α γ m j)) =
    taggedKernel (independentCorrectionKernel
      (S.jointLevelKernel O (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a ha)
      (S.jointLevelKernel O (2 ^ (j + 1)) (levelSteps ℓ α γ m (2 ^ (j + 1))) a ha)
      (S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha) p)
      (correctionHorizon ℓ α γ m j) := by
  rw [taggedKernel, ← S.correction_original_history O γ m j p a ha,
    ← Kernel.map_comp_right _ (f := correctionTranscriptRead ℓ α γ m j p a)
      (g := fun r : Euclid dy => (r, correctionHorizon ℓ α γ m j))
      (correctionTranscriptRead_measurable ℓ α γ m j p a ha) (measurable_id.prodMk measurable_const)]
  rfl

end SCObjective
end FreshGradientMinimax
