import FreshGradientMinimax.ParameterEstimator
import FreshGradientMinimax.ParameterCarry
import FreshGradientMinimax.EpochProgram

/-! An epoch whose known regularizer is selected by a continuous input
parameter. The parameter is retained through every accelerated step and
fast refresh; fixing it gives the previously analysed costed epoch. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ} {Θ : Type} [MeasurableSpace Θ]

def parameterEpochQuery (τ : ℝ) (z : Θ × EpochState dx dy) : Θ × Joint dx dy :=
  (z.1, (z.2.1, accelerationQuery τ z.2.2))

theorem parameterEpochQuery_measurable (τ : ℝ) :
    Measurable (parameterEpochQuery (dx := dx) (dy := dy) (Θ := Θ) τ) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    ((accelerationQuery_continuous τ).measurable.comp measurable_snd.snd))

def parameterEpochUpdate (τ m H : ℝ) (z : (Θ × EpochState dx dy) × Euclid dy) : Θ × EpochState dx dy :=
  (z.1.1, referenceAccelerationUpdate τ m H (z.1.2, z.2))

theorem parameterEpochUpdate_measurable (τ m H : ℝ) :
    Measurable (parameterEpochUpdate (dx := dx) (dy := dy) (Θ := Θ) τ m H) :=
  measurable_fst.fst.prodMk ((referenceAccelerationUpdate_continuous τ m H).measurable.comp
    (measurable_fst.snd.prodMk measurable_snd))

def parameterEpochStepProgram (dx dy : ℕ) (ℓ α σ ρ m H e : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) :
    OracleProgram dx dy (Θ × EpochState dx dy) (Θ × EpochState dx dy) :=
  (((parameterEstimatorProgram dx dy ℓ α σ ρ m e r hr).batch b).precompose
    (parameterEpochQuery (Real.sqrt (m / H))) (parameterEpochQuery_measurable _)).update
    (parameterEpochUpdate (Real.sqrt (m / H)) m H) (parameterEpochUpdate_measurable _ _ _)

def parameterEpochInitial (z : Θ × Joint dx dy) : Θ × EpochState dx dy := (z.1, (z.2.1, (z.2.2, z.2.2)))

theorem parameterEpochInitial_measurable : Measurable (parameterEpochInitial (dx := dx) (dy := dy) (Θ := Θ)) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_snd.snd))

def parameterEpochPhaseProgram (dx dy : ℕ) (ℓ α σ m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) :
    OracleProgram dx dy (Θ × Joint dx dy) (Θ × EpochState dx dy) :=
  ((parameterEpochStepProgram dx dy ℓ α σ epochRho m H e r hr (epochBatch m H e σ E)).iterate
    (epochSteps m H)).precompose parameterEpochInitial parameterEpochInitial_measurable

def parameterFullEpochProgram (dx dy : ℕ) (ℓ α σ m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) :
    OracleProgram dx dy (Θ × Joint dx dy) (Θ × Joint dx dy) :=
  (parameterEpochPhaseProgram dx dy ℓ α σ m H e E r hr).chain
    (((refreshProgram dx dy ℓ α σ m E).precompose (fun t : EpochState dx dy => (t.1, t.2.1))
      (measurable_fst.prodMk measurable_snd.fst)).carryParameter)

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem parameterEpochStepProgram_fiber (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (θ : Θ) (b : ℕ) :
    ((parameterEpochStepProgram dx dy ℓ α σ ρ m H e r hr b).lawKernel O.kernel).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      (S.costedJointEpochStepKernel O ρ m H e (fun v => r (θ, v)) (hr.comp measurable_prodMk_left) b).map
        (costedMap (fun x => (θ, x))) := by
  rw [parameterEpochStepProgram, OracleProgram.update_law, OracleProgram.precompose_law, costedJointEpochStepKernel]
  apply costedUpdateKernel_transport _ _ (fun x => (θ, x)) measurable_prodMk_left id measurable_id
    (fun x => (θ, x)) measurable_prodMk_left _ (referenceAccelerationUpdate_continuous _ _ _).measurable
    _ (parameterEpochUpdate_measurable _ _ _)
  · change _ = ((costedBatchKernel (S.jointCostedEstimatorKernel O ρ m e (fun v => r (θ, v))
      (hr.comp measurable_prodMk_left)) b).comap
        (fun z : EpochState dx dy => (z.1, accelerationQuery (Real.sqrt (m / H)) z.2))
          (measurable_fst.prodMk ((accelerationQuery_continuous _).measurable.comp measurable_snd))).map id
    rw [Kernel.map_id]
    change ((((parameterEstimatorProgram dx dy ℓ α σ ρ m e r hr).batch b).lawKernel O.kernel).comap
      (fun x => (θ, x)) measurable_prodMk_left).comap
        (fun z : EpochState dx dy => (z.1, accelerationQuery (Real.sqrt (m / H)) z.2))
          (measurable_fst.prodMk ((accelerationQuery_continuous _).measurable.comp measurable_snd)) = _
    rw [S.parameterEstimatorProgram_batch_fiber]
  · intro x y; rfl

theorem parameterEpochPhaseProgram_fiber (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (θ : Θ) :
    ((parameterEpochPhaseProgram dx dy ℓ α σ m H e E r hr).lawKernel O.kernel).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      (S.costedEpochPhaseKernel O m H e E (fun v => r (θ, v)) (hr.comp measurable_prodMk_left)).map
        (costedMap (fun x => (θ, x))) := by
  rw [parameterEpochPhaseProgram, OracleProgram.precompose_law, OracleProgram.iterate_law]
  change ((costedIterate ((parameterEpochStepProgram dx dy ℓ α σ epochRho m H e r hr
    (epochBatch m H e σ E)).lawKernel O.kernel) (epochSteps m H)).comap (fun x => (θ, x))
      measurable_prodMk_left).comap (fun z : Joint dx dy => (z.1, (z.2, z.2)))
        (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)) = _
  rw [costedIterate_transport _ _ _ measurable_prodMk_left
    (S.parameterEpochStepProgram_fiber O epochRho m H e r hr θ (epochBatch m H e σ E)),
    Kernel.comap_map_comm _ (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))
      (costedMap_measurable measurable_prodMk_left)]
  rfl

theorem parameterFullEpochProgram_fiber (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (θ : Θ) :
    ((parameterFullEpochProgram dx dy ℓ α σ m H e E r hr).lawKernel O.kernel).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      (S.costedFullEpochKernel O m H e E (fun v => r (θ, v)) (hr.comp measurable_prodMk_left)).map
        (costedMap (fun x => (θ, x))) := by
  rw [parameterFullEpochProgram, OracleProgram.chain_law, ← S.fullEpochProgram_law O m H e E _ _,
    fullEpochProgram, OracleProgram.chain_law]
  apply costedCompose_transport _ _ _ _ (fun x => (θ, x)) measurable_prodMk_left
    (fun x => (θ, x)) measurable_prodMk_left (fun x => (θ, x)) measurable_prodMk_left
  · rw [S.epochPhaseProgram_law]
    exact S.parameterEpochPhaseProgram_fiber O m H e E r hr θ
  · exact OracleProgram.carryParameter_fiber _ O.kernel θ

end SCObjective
end FreshGradientMinimax
