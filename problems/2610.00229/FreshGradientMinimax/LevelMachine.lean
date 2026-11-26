import FreshGradientMinimax.FastBatchMachine
import FreshGradientMinimax.MachineSequence

/-! The whole level estimator executes n minibatch primal steps followed
by one fresh dual minibatch at the resulting random point. Its internal
dual output is read from the original Algorithm transcript. The policy
contains no access to the unknown objective or oracle. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ}

abbrev LevelMachineState (dx dy : ℕ) := (Joint dx dy × Euclid dx) × Euclid dy

def levelInitial (q : Joint dx dy) : LevelMachineState dx dy := (batchInitial q, 0)

theorem levelInitial_measurable : Measurable (levelInitial (dx := dx) (dy := dy)) :=
  batchInitial_measurable.prodMk measurable_const

def dualBatchMachine (dx dy : ℕ) : OracleMachine dx dy (LevelMachineState dx dy) where
  query _ s := s.1.1
  update _ z := (z.1.1, z.1.2 + z.2.2)
  output _ s := s.1.1.1
  query_measurable _ := measurable_fst.fst
  update_measurable _ := measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd.snd)
  output_measurable _ := measurable_fst.fst.fst

def dualBatchEmbed (s : Joint dx dy × Euclid dy) : LevelMachineState dx dy := ((s.1, 0), s.2)

theorem dualBatchEmbed_measurable : Measurable (dualBatchEmbed (dx := dx) (dy := dy)) :=
  (measurable_fst.prodMk measurable_const).prodMk measurable_snd

def levelRead (b : ℕ) (a : Euclid dy → Euclid dy) (s : LevelMachineState dx dy) : Euclid dy :=
  -((b : ℝ)⁻¹ • s.2) + a s.1.1.2

theorem levelRead_measurable (b : ℕ) (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    Measurable (levelRead (dx := dx) b a) :=
  (measurable_const.smul measurable_snd).neg.add (ha.comp measurable_fst.fst.snd)

def levelMachine (dx dy : ℕ) (ℓ : ℝ) (b n : ℕ) : OracleMachine dx dy (LevelMachineState dx dy) :=
  ((fastBatchMachine ℓ b).carry).sequence (dualBatchMachine dx dy) (n * b)

def levelAlgorithm (dx dy : ℕ) (ℓ : ℝ) (b n : ℕ) : Algorithm dx dy (Joint dx dy) :=
  (levelMachine dx dy ℓ b n).compile levelInitial levelInitial_measurable

def levelTranscriptRead (ℓ : ℝ) (b n : ℕ) (a : Euclid dy → Euclid dy)
    (h : RunState dx dy (Joint dx dy) ((n + 1) * b)) : Euclid dy :=
  levelRead b a ((levelMachine dx dy ℓ b n).replay levelInitial ((n + 1) * b) h)

theorem levelTranscriptRead_measurable (ℓ : ℝ) (b n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    Measurable (levelTranscriptRead (dx := dx) ℓ b n a) :=
  (levelRead_measurable b a ha).comp
    ((levelMachine dx dy ℓ b n).replay_measurable levelInitial levelInitial_measurable _)

def originalLevelKernel (ℓ : ℝ) (b n : ℕ) (a : Euclid dy → Euclid dy)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel (Joint dx dy) (Euclid dy) :=
  ((levelAlgorithm dx dy ℓ b n).historyKernel K ((n + 1) * b)).map (levelTranscriptRead ℓ b n a)

theorem dualBatchMachine_run (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (b : ℕ) :
    (dualBatchMachine dx dy).runKernel levelInitial levelInitial_measurable K b =
      ((batchMachine Prod.snd measurable_snd (fun _ => (0 : Euclid dx)) measurable_const).runKernel
        batchInitial batchInitial_measurable K b).map dualBatchEmbed := by
  exact OracleMachine.runKernel_transport _ (dualBatchMachine dx dy) dualBatchEmbed dualBatchEmbed_measurable
    batchInitial batchInitial_measurable K
    (fun j => OracleMachine.stepKernel_transport _ _ _ _ K j (fun _ => rfl) (fun _ _ => rfl)) b

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem dualBatchMachine_read (O : FreshOracle S.toNCObjective σ) (b : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((dualBatchMachine dx dy).runKernel levelInitial levelInitial_measurable O.kernel b).map (levelRead b a) =
      S.jointLevelReadKernel O b a ha := by
  rw [dualBatchMachine_run, ← Kernel.map_comp_right _ dualBatchEmbed_measurable (levelRead_measurable b a ha)]
  apply Kernel.ext
  rintro ⟨u, v⟩
  rw [Kernel.map_apply _ ((levelRead_measurable b a ha).comp dualBatchEmbed_measurable),
    batchMachine_run, Measure.map_map (f := fun r : Euclid dy => ((u, v), r))
      ((levelRead_measurable b a ha).comp dualBatchEmbed_measurable) (measurable_const.prodMk measurable_id),
    S.jointLevelReadKernel_apply, S.levelReadKernel_apply, batchKernel,
    Kernel.map_apply (f := fun r : Euclid dy => (b : ℝ)⁻¹ • r) _ (measurable_const.smul measurable_id),
    Measure.map_map (f := fun r : Euclid dy => (b : ℝ)⁻¹ • r)
      (g := fun r : Euclid dy => -r + a v) (measurable_id.neg.add measurable_const)
      (measurable_const.smul measurable_id)]
  rfl

theorem levelMachine_run (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((levelMachine dx dy ℓ b n).runKernel levelInitial levelInitial_measurable O.kernel ((n + 1) * b)).map
      (levelRead b a) = S.jointLevelKernel O b n a ha := by
  rw [Nat.add_mul, Nat.one_mul, levelMachine, OracleMachine.sequence_run]
  have hfast : ((fastBatchMachine (dx := dx) (dy := dy) ℓ b).carry).runKernel
      levelInitial levelInitial_measurable O.kernel (n * b) = (S.jointFastRunKernel O b n).map levelInitial := by
    change ((fastBatchMachine (dx := dx) (dy := dy) ℓ b).carry).runKernel
      (fun q => (batchInitial q, (0 : Euclid dy))) (batchInitial_measurable.prodMk measurable_const)
      O.kernel (n * b) = _
    rw [OracleMachine.carry_run_fixed (fastBatchMachine ℓ b) (0 : Euclid dy) batchInitial batchInitial_measurable,
      S.fastBatchMachine_run O hb,
      ← Kernel.map_comp_right _ (f := batchInitial) (g := fun s => (s, (0 : Euclid dy)))
        batchInitial_measurable (measurable_id.prodMk measurable_const)]
    rfl
  rw [hfast, Kernel.comp_map _ _ levelInitial_measurable,
    OracleMachine.runKernel_precompose, Kernel.map_comp, S.dualBatchMachine_read O b a ha]
  rfl

theorem originalLevelKernel_eq (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    originalLevelKernel ℓ b n a O.kernel = S.jointLevelKernel O b n a ha := by
  rw [← S.levelMachine_run O hb n a ha, OracleMachine.runKernel_eq_history,
    ← Kernel.map_comp_right _
      ((levelMachine dx dy ℓ b n).replay_measurable levelInitial levelInitial_measurable _)
      (levelRead_measurable b a ha)]
  rfl

theorem level_original_history (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((levelAlgorithm dx dy ℓ b n).historyKernel O.kernel ((n + 1) * b)).map
      (levelTranscriptRead ℓ b n a) = S.jointLevelKernel O b n a ha :=
  S.originalLevelKernel_eq O hb n a ha

theorem level_original_law (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (ν : Measure (Joint dx dy)) :
    (((levelAlgorithm dx dy ℓ b n).historyKernel O.kernel ((n + 1) * b)) ∘ₘ ν).map
      (levelTranscriptRead ℓ b n a) = S.jointLevelKernel O b n a ha ∘ₘ ν := by
  rw [Measure.map_comp _ _ (levelTranscriptRead_measurable ℓ b n a ha), S.level_original_history O hb n a ha]

theorem level_original_tagged_kernel (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    ((levelAlgorithm dx dy ℓ b n).historyKernel O.kernel ((n + 1) * b)).map
      (fun h => (levelTranscriptRead ℓ b n a h, (n + 1) * b)) =
      taggedKernel (S.jointLevelKernel O b n a ha) ((n + 1) * b) := by
  rw [taggedKernel, ← S.level_original_history O hb n a ha,
    ← Kernel.map_comp_right _ (f := levelTranscriptRead ℓ b n a)
      (g := fun r : Euclid dy => (r, (n + 1) * b)) (levelTranscriptRead_measurable ℓ b n a ha)
      (measurable_id.prodMk measurable_const)]
  rfl

end SCObjective
end FreshGradientMinimax
