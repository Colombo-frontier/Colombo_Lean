import FreshGradientMinimax.OracleMachine
import FreshGradientMinimax.SequentialBatch
import FreshGradientMinimax.OracleBatch

/-! A minibatch implemented by exactly b calls to the original joint
oracle. The fixed query and running sum are internal state; projection
occurs only after each original response. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy d : ℕ}

def batchMachine (p : Joint dx dy → Euclid d) (hp : Measurable p)
    (out : Euclid d → Euclid dx) (ho : Measurable out) : OracleMachine dx dy (Joint dx dy × Euclid d) where
  query _ := Prod.fst
  update _ z := (z.1.1, z.1.2 + p z.2)
  output n z := out ((n : ℝ)⁻¹ • z.2)
  query_measurable _ := measurable_fst
  update_measurable _ := measurable_fst.fst.prodMk (measurable_fst.snd.add (hp.comp measurable_snd))
  output_measurable _ := ho.comp (measurable_const.smul measurable_snd)

def batchInitial (q : Joint dx dy) : Joint dx dy × Euclid d := (q, 0)

theorem batchInitial_measurable : Measurable (batchInitial (dx := dx) (dy := dy) (d := d)) :=
  measurable_id.prodMk measurable_const

theorem batchMachine_step_fixed (p : Joint dx dy → Euclid d) (hp : Measurable p)
    (out : Euclid d → Euclid dx) (ho : Measurable out)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (q : Joint dx dy) :
    ((batchMachine p hp out ho).stepKernel K 0).comap (fun s => (q, s))
      (measurable_const.prodMk measurable_id) =
    (addSampleKernel ((K q).map p)).map (fun s => (q, s)) := by
  letI : IsProbabilityMeasure ((K q).map p) := isProbabilityMeasure_map hp.aemeasurable
  apply Kernel.ext
  intro s
  rw [Kernel.comap_apply, OracleMachine.stepKernel_apply,
    Kernel.map_apply (f := fun s : Euclid d => (q, s)) _ (measurable_const.prodMk measurable_id),
    addSampleKernel_apply,
    Measure.map_map (f := fun r : Euclid d => s + r) (g := fun r : Euclid d => (q, r))
      (measurable_const.prodMk measurable_id) (measurable_const.add measurable_id)]
  simp only [Function.comp_def]
  rw [Measure.map_map (g := fun r : Euclid d => (q, s + r))
      (measurable_const.prodMk (measurable_const.add measurable_id)) hp]
  rfl

theorem batchMachine_run (p : Joint dx dy → Euclid d) (hp : Measurable p)
    (out : Euclid d → Euclid dx) (ho : Measurable out)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) (q : Joint dx dy) :
    (batchMachine p hp out ho).runKernel batchInitial batchInitial_measurable K n q =
      (iidSumKernel (K.map p) n q).map (fun s => (q, s)) := by
  letI : IsProbabilityMeasure ((K q).map p) := isProbabilityMeasure_map hp.aemeasurable
  letI : IsMarkovKernel (K.map p) := Kernel.IsMarkovKernel.map _ hp
  rw [OracleMachine.runKernel_homogeneous _ _ _ K ((batchMachine p hp out ho).stepKernel K 0)
    (fun _ => rfl), Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  have ht := congrArg (fun L : Kernel (Euclid d) (Joint dx dy × Euclid d) => L 0)
    (iterateKernel_transport (addSampleKernel ((K q).map p)) ((batchMachine p hp out ho).stepKernel K 0)
      (fun s => (q, s)) (measurable_const.prodMk measurable_id) (batchMachine_step_fixed p hp out ho K q) n)
  dsimp only at ht
  rw [Kernel.comap_apply, Kernel.map_apply (f := fun s : Euclid d => (q, s)) _
    (measurable_const.prodMk measurable_id), sequential_sum_apply] at ht
  have he := iidSumKernel_congr_at (Kernel.const Unit ((K q).map p)) (K.map p) () q
    (by rw [Kernel.const_apply, Kernel.map_apply _ hp]) n
  rw [he] at ht
  exact ht

theorem batchMachine_compiled_output (p : Joint dx dy → Euclid d) (hp : Measurable p)
    (out : Euclid d → Euclid dx) (ho : Measurable out)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (b : ℕ) :
    ((batchMachine p hp out ho).compile batchInitial batchInitial_measurable).outputKernel K b =
      (batchKernel (K.map p) b).map out := by
  rw [OracleMachine.compiled_outputKernel]
  apply Kernel.ext
  intro q
  rw [Kernel.map_apply _ ((batchMachine p hp out ho).output_measurable b),
    batchMachine_run p hp out ho K b q,
    Measure.map_map (f := fun s : Euclid d => (q, s))
      ((batchMachine p hp out ho).output_measurable b) (measurable_const.prodMk measurable_id),
    Kernel.map_apply _ ho, batchKernel,
    Kernel.map_apply (f := fun r : Euclid d => (b : ℝ)⁻¹ • r) _ (measurable_const.smul measurable_id),
    Measure.map_map (f := fun r : Euclid d => (b : ℝ)⁻¹ • r) ho (measurable_const.smul measurable_id)]
  rfl

def primalBatchAlgorithm (dx dy : ℕ) : Algorithm dx dy (Joint dx dy) :=
  (batchMachine Prod.fst measurable_fst id measurable_id).compile batchInitial batchInitial_measurable

theorem primalBatchAlgorithm_output {L μ σ : ℝ} {O : NCObjective dx dy L μ}
    (K : FreshOracle O σ) (b : ℕ) :
    (primalBatchAlgorithm dx dy).outputKernel K.kernel b = batchKernel K.primalKernel b := by
  have h := batchMachine_compiled_output (dx := dx) (dy := dy) Prod.fst measurable_fst id measurable_id K.kernel b
  rw [Kernel.map_id] at h
  exact h

theorem primalBatchAlgorithm_law {L μ σ : ℝ} {O : NCObjective dx dy L μ}
    (K : FreshOracle O σ) (ν : Measure (Joint dx dy)) (b : ℕ) :
    (primalBatchAlgorithm dx dy).outputLaw ν K.kernel b = batchKernel K.primalKernel b ∘ₘ ν := by
  rw [Algorithm.outputLaw, primalBatchAlgorithm_output]

end FreshGradientMinimax
