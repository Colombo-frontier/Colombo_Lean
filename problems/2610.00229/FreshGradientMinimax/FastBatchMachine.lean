import FreshGradientMinimax.BatchMachine
import FreshGradientMinimax.MachineComposition
import FreshGradientMinimax.FastRefresh

/-! Actual original-query implementation of all minibatch fast-gradient
steps. The compiled policy depends on the step size and batch size, not
on the objective or oracle. After n*b calls its law is the analysed run. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ}

def fastBatchFinish (ℓ : ℝ) (b : ℕ) (s : Joint dx dy × Euclid dx) : Joint dx dy × Euclid dx :=
  ((s.1.1 - ℓ⁻¹ • ((b : ℝ)⁻¹ • s.2), s.1.2), 0)

theorem fastBatchFinish_measurable (ℓ : ℝ) (b : ℕ) :
    Measurable (fastBatchFinish (dx := dx) (dy := dy) ℓ b) :=
  ((measurable_fst.fst.sub (measurable_const.smul (measurable_const.smul measurable_snd))).prodMk
    measurable_fst.snd).prodMk measurable_const

def fastBlockMachine (ℓ : ℝ) (b : ℕ) : OracleMachine dx dy (Joint dx dy × Euclid dx) :=
  (batchMachine Prod.fst measurable_fst id measurable_id).endUpdate b
    (fastBatchFinish ℓ b) (fastBatchFinish_measurable ℓ b)

def fastBatchMachine (ℓ : ℝ) (b : ℕ) : OracleMachine dx dy (Joint dx dy × Euclid dx) :=
  ((fastBlockMachine ℓ b).periodic b).withOutput (fun _ s => s.1.1) (fun _ => measurable_fst.fst)

def fastBatchAlgorithm (dx dy : ℕ) (ℓ : ℝ) (b : ℕ) : Algorithm dx dy (Joint dx dy) :=
  (fastBatchMachine ℓ b).compile batchInitial batchInitial_measurable

def fastBatchMethod (dx dy : ℕ) (ℓ : ℝ) (b : ℕ) (u : Euclid dx) (v : Euclid dy) : RandomizedAlgorithm dx dy where
  Seed := Joint dx dy
  seedLaw := Measure.dirac (u, v)
  policy := fastBatchAlgorithm dx dy ℓ b

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem fastBlockMachine_transport (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) :
    (kernelSegment ((fastBlockMachine (dx := dx) (dy := dy) ℓ b).stepKernel O.kernel) 0 b).comap
      batchInitial batchInitial_measurable = (S.jointFastStepKernel O b).map batchInitial := by
  rw [← Kernel.comp_deterministic_eq_comap, ← OracleMachine.runKernel_segment,
    fastBlockMachine, OracleMachine.endUpdate_run _ b hb]
  apply Kernel.ext
  intro q
  rw [Kernel.map_apply _ (fastBatchFinish_measurable ℓ b),
    batchMachine_run Prod.fst measurable_fst id measurable_id,
    Measure.map_map (f := fun s : Euclid dx => (q, s)) (fastBatchFinish_measurable ℓ b)
      (measurable_const.prodMk measurable_id), Kernel.map_apply _ batchInitial_measurable]
  rcases q with ⟨u, v⟩
  rw [S.jointFastStepKernel_apply,
    Measure.map_map (f := fun r : Euclid dx => (u - ℓ⁻¹ • r, v)) batchInitial_measurable
      ((measurable_const.sub (measurable_const.smul measurable_id)).prodMk measurable_const),
    batchKernel, Kernel.map_apply (f := fun r : Euclid dx => (b : ℝ)⁻¹ • r) _
      (measurable_const.smul measurable_id),
    Measure.map_map (f := fun r : Euclid dx => (b : ℝ)⁻¹ • r)
      (g := batchInitial ∘ fun r : Euclid dx => (u - ℓ⁻¹ • r, v))
      (batchInitial_measurable.comp ((measurable_const.sub (measurable_const.smul measurable_id)).prodMk measurable_const))
      (measurable_const.smul measurable_id)]
  rfl

theorem fastBatchMachine_run (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    (fastBatchMachine (dx := dx) (dy := dy) ℓ b).runKernel batchInitial batchInitial_measurable O.kernel (n * b) =
      (S.jointFastRunKernel O b n).map batchInitial := by
  rw [fastBatchMachine, OracleMachine.runKernel_withOutput, OracleMachine.periodic_run_blocks,
    Kernel.comp_deterministic_eq_comap]
  exact iterateKernel_transport (S.jointFastStepKernel O b)
    (kernelSegment ((fastBlockMachine ℓ b).stepKernel O.kernel) 0 b)
    batchInitial batchInitial_measurable (S.fastBlockMachine_transport O hb) n

theorem fastBatchAlgorithm_output (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    (fastBatchAlgorithm dx dy ℓ b).outputKernel O.kernel (n * b) = (S.jointFastRunKernel O b n).map Prod.fst := by
  rw [fastBatchAlgorithm, OracleMachine.compiled_outputKernel, S.fastBatchMachine_run O hb,
    ← Kernel.map_comp_right _ batchInitial_measurable ((fastBatchMachine ℓ b).output_measurable (n * b))]
  rfl

theorem fastBatchAlgorithm_joint_state (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    ((fastBatchAlgorithm dx dy ℓ b).historyKernel O.kernel (n * b)).map
      (fun h => ((fastBatchMachine (dx := dx) (dy := dy) ℓ b).replay batchInitial (n * b) h).1) =
        S.jointFastRunKernel O b n := by
  have h := congrArg (fun L : Kernel (Joint dx dy) (Joint dx dy × Euclid dx) => L.map Prod.fst)
    (S.fastBatchMachine_run O hb n)
  dsimp only at h
  rw [OracleMachine.runKernel_eq_history,
    ← Kernel.map_comp_right _ ((fastBatchMachine ℓ b).replay_measurable batchInitial batchInitial_measurable (n * b))
      measurable_fst,
    ← Kernel.map_comp_right _ batchInitial_measurable measurable_fst] at h
  change _ = (S.jointFastRunKernel O b n).map id at h
  rw [Kernel.map_id] at h
  exact h

theorem fastBatchAlgorithm_fixed (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (n : ℕ) (u : Euclid dx) (v : Euclid dy) :
    (fastBatchAlgorithm dx dy ℓ b).outputKernel O.kernel (n * b) (u, v) = S.fastRunKernel O b v n u := by
  rw [S.fastBatchAlgorithm_output O hb, Kernel.map_apply _ measurable_fst, S.jointFastRunKernel_apply,
    Measure.map_map (f := fun w : Euclid dx => (w, v)) measurable_fst (measurable_id.prodMk measurable_const)]
  exact Measure.map_id

theorem fastBatchAlgorithm_error (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (hαℓ : α ≤ ℓ) (n : ℕ) (u : Euclid dx) (v : Euclid dy) :
    Integrable (fun w => ‖w - S.sliceMin v‖ ^ 2)
      ((fastBatchAlgorithm dx dy ℓ b).outputKernel O.kernel (n * b) (u, v)) ∧
    (∫ w, ‖w - S.sliceMin v‖ ^ 2 ∂(fastBatchAlgorithm dx dy ℓ b).outputKernel O.kernel (n * b) (u, v)) ≤
      (1 - α / ℓ) ^ n * ‖u - S.sliceMin v‖ ^ 2 + σ ^ 2 / (α * ℓ * b) := by
  rw [S.fastBatchAlgorithm_fixed O hb]
  exact ⟨S.fastRunKernel_square_integrable O hb v n u, S.fastRunKernel_error_floor O hb hαℓ v n u⟩

theorem fastBatchMethod_law (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (n : ℕ) (u : Euclid dx) (v : Euclid dy) :
    (fastBatchMethod dx dy ℓ b u v).outputLaw O.kernel (n * b) = S.fastRunKernel O b v n u := by
  change (Measure.dirac (u, v)).bind ((fastBatchAlgorithm dx dy ℓ b).outputKernel O.kernel (n * b)) = _
  rw [Measure.dirac_bind (Kernel.measurable _), S.fastBatchAlgorithm_fixed O hb]

theorem fastBatchMethod_error (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (hαℓ : α ≤ ℓ) (n : ℕ) (u : Euclid dx) (v : Euclid dy) :
    Integrable (fun w => ‖w - S.sliceMin v‖ ^ 2) ((fastBatchMethod dx dy ℓ b u v).outputLaw O.kernel (n * b)) ∧
    (∫ w, ‖w - S.sliceMin v‖ ^ 2 ∂(fastBatchMethod dx dy ℓ b u v).outputLaw O.kernel (n * b)) ≤
      (1 - α / ℓ) ^ n * ‖u - S.sliceMin v‖ ^ 2 + σ ^ 2 / (α * ℓ * b) := by
  rw [S.fastBatchMethod_law O hb]
  exact ⟨S.fastRunKernel_square_integrable O hb v n u, S.fastRunKernel_error_floor O hb hαℓ v n u⟩

end SCObjective
end FreshGradientMinimax
