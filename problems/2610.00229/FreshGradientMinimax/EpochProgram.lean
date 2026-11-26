import FreshGradientMinimax.EstimatorProgram
import FreshGradientMinimax.ProgramUpdate

/-! One original-query program for the entire accelerated epoch and fast
refresh. Every internal estimator has its own independent initial seed;
its variable number of calls is accounted for by program composition. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def epochStepProgram (dx dy : ℕ) (ℓ α σ ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    OracleProgram dx dy (EpochState dx dy) (EpochState dx dy) :=
  (((relativeEstimatorProgram dx dy ℓ α σ ρ m e r hr).batch b).precompose
    (fun z : EpochState dx dy => (z.1, accelerationQuery (Real.sqrt (m / H)) z.2))
    (measurable_fst.prodMk ((accelerationQuery_continuous _).measurable.comp measurable_snd))).update
    (referenceAccelerationUpdate (Real.sqrt (m / H)) m H)
    (referenceAccelerationUpdate_continuous _ _ _).measurable

def epochPhaseProgram (dx dy : ℕ) (ℓ α σ m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    OracleProgram dx dy (Joint dx dy) (EpochState dx dy) :=
  ((epochStepProgram dx dy ℓ α σ epochRho m H e r hr (epochBatch m H e σ E)).iterate (epochSteps m H)).precompose
    (fun z : Joint dx dy => (z.1, (z.2, z.2))) (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))

def refreshProgram (dx dy : ℕ) (ℓ α σ m E : ℝ) : OracleProgram dx dy (Joint dx dy) (Joint dx dy) where
  Seed := Unit
  seedLaw := Measure.dirac ()
  State := Joint dx dy × Euclid dx
  machine _ := fastBatchMachine ℓ (refreshBatch ℓ α σ m E)
  init _ := batchInitial
  init_measurable _ := batchInitial_measurable
  read _ := Prod.fst
  read_measurable _ := measurable_fst
  calls _ := refreshSteps ℓ α * refreshBatch ℓ α σ m E

def fullEpochProgram (dx dy : ℕ) (ℓ α σ m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : OracleProgram dx dy (Joint dx dy) (Joint dx dy) :=
  (epochPhaseProgram dx dy ℓ α σ m H e E r hr).chain
    ((refreshProgram dx dy ℓ α σ m E).precompose (fun t : EpochState dx dy => (t.1, t.2.1))
      (measurable_fst.prodMk measurable_snd.fst))

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem epochStepProgram_law (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    (epochStepProgram dx dy ℓ α σ ρ m H e r hr b).lawKernel O.kernel =
      S.costedJointEpochStepKernel O ρ m H e r hr b := by
  rw [epochStepProgram, OracleProgram.update_law, OracleProgram.precompose_law, OracleProgram.batch_law,
    S.relativeEstimatorProgram_law]
  rfl

theorem epochPhaseProgram_law (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (epochPhaseProgram dx dy ℓ α σ m H e E r hr).lawKernel O.kernel = S.costedEpochPhaseKernel O m H e E r hr := by
  rw [epochPhaseProgram, OracleProgram.precompose_law, OracleProgram.iterate_law, S.epochStepProgram_law]
  rfl

theorem refreshProgram_law (O : FreshOracle S.toNCObjective σ) (m E : ℝ) :
    (refreshProgram dx dy ℓ α σ m E).lawKernel O.kernel =
      taggedKernel (S.refreshKernel O m E) (refreshSteps ℓ α * refreshBatch ℓ α σ m E) := by
  change mixtureKernel (Measure.dirac ()) ((refreshProgram dx dy ℓ α σ m E).branchKernel O.kernel) = _
  rw [mixtureKernel_dirac]
  change taggedKernel _ _ = _
  dsimp only [refreshProgram]
  rw [S.fastBatchMachine_run O (refreshBatch_pos ℓ α σ m E),
    ← Kernel.map_comp_right _ (f := batchInitial) (g := Prod.fst) batchInitial_measurable measurable_fst]
  change taggedKernel ((S.refreshKernel O m E).map id) _ = _
  rw [Kernel.map_id]

theorem fullEpochProgram_law (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (fullEpochProgram dx dy ℓ α σ m H e E r hr).lawKernel O.kernel = S.costedFullEpochKernel O m H e E r hr := by
  rw [fullEpochProgram, OracleProgram.chain_law, S.epochPhaseProgram_law, OracleProgram.precompose_law,
    S.refreshProgram_law]
  unfold costedFullEpochKernel refreshFromStateKernel
  rw [taggedKernel, taggedKernel, Kernel.comap_map_comm _
    (g := fun r : Joint dx dy => (r, refreshSteps ℓ α * refreshBatch ℓ α σ m E)) _
    (measurable_id.prodMk measurable_const)]

theorem fullEpochProgram_original (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (fullEpochProgram dx dy ℓ α σ m H e E r hr).originalKernel O.kernel = S.costedFullEpochKernel O m H e E r hr := by
  rw [OracleProgram.originalKernel_eq_law, S.fullEpochProgram_law]

end SCObjective
end FreshGradientMinimax
