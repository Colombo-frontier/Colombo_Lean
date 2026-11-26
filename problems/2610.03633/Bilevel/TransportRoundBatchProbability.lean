import Bilevel.TransportControllerMachineReverseProbability

/-! Finite edge union for the concrete same-run batch failure event. Both
directions are bounded under the same original probability law; no
independence between edges, directions, or rounds is used. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportNetworkAuxiliary TransportControllerEdge TransportControllerMachine
set_option maxHeartbeats 800000

def runBatchBad {H : Type*} {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) : Prop :=
  batchFailure hT t (frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t) z
    (fun e => runPairs hT choose respond (prefixNames n T) (memory,seed T hT z) z e t)

def forwardBudget (n p t r : ℕ) : ℝ≥0∞ :=
  ((1+historyProbes n p 1 1 t : ℕ):ℝ≥0∞)*budget ((size n p 1 1 t+p)+1) r

def reverseBudget (n p t r : ℕ) : ℝ≥0∞ :=
  ((1+((size n p 1 1 t+p)+historyProbes n p 1 1 t) : ℕ):ℝ≥0∞)*budget (reverseDimension n (size n p 1 1 t+p)) r

def batchBudget (n p t r : ℕ) : ℝ≥0∞ := (n:ℝ≥0∞)*(forwardBudget n p t r+reverseBudget n p t r)

theorem measure_exists_fin_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (P : Fin n → Ω → Prop) (b : ℝ≥0∞) (hb : ∀ i,μ {s | P i s}≤b) :
    μ {s | ∃ i,P i s}≤(n:ℝ≥0∞)*b := by
  have he : {s | ∃ i,P i s}=⋃ i,{s | P i s} := by ext s; simp
  rw [he]
  calc
    _ ≤ ∑' i,μ {s | P i s} := measure_iUnion_le _
    _ ≤ ∑' _i : Fin n,b := ENNReal.tsum_le_tsum hb
    _ = _ := by simp

theorem actual_batch_failure_probability {n D T p k : ℕ} (H : Memory) (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (t r : ℕ) (hrpos : 0<r)
    (hD : T+(1+((size n p 1 1 t+p)+historyProbes n p 1 1 t))+r≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k)) {s | runBatchBad hT choose respond s.1 s.2.1 t}≤batchBudget n p t r := by
  let g := fun s : H × Sample n D k => frozenAt hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 t
  let P := fun s : H × Sample n D k => fun e => runPairs hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 e t
  let W := fun s : H × Sample n D k => known (postGrant T hT t (g s) s.2.1)
  let F := fun e s => forwardMonitor hT t (g s) s.2.1 (P s) (W s) e
  let R := fun e s => reverseMonitor hT t (g s) s.2.1 (P s) (forwardLedger (g s) s.2.1 (W s)) e
  have he : {s : H × Sample n D k | runBatchBad hT choose respond s.1 s.2.1 t}=
      {s | ∃ e,F e s}∪{s | ∃ e,R e s} := by
    ext s
    exact batchFailure_distinct hT t (g s) s.2.1 (P s)
  have hf : ∀ e,(ρ.prod (TransportNetworkAuxiliary.law n D k)) {s | F e s}≤forwardBudget n p t r := by
    intro e
    exact actual_forward_failure_probability H hT e choose hc respond hr ρ t r hrpos (by omega)
  have hr' : ∀ e,(ρ.prod (TransportNetworkAuxiliary.law n D k)) {s | R e s}≤reverseBudget n p t r := by
    intro e
    exact actual_reverse_failure_probability H hT e choose hc respond hr ρ t r hrpos hD
  rw [he,batchBudget,mul_add]
  exact (measure_union_le _ _).trans
    (add_le_add (measure_exists_fin_le _ F _ hf) (measure_exists_fin_le _ R _ hr'))

end Bilevel.TransportRound
