import Bilevel.TransportRoundBatchEnergy
import Bilevel.TransportRoundDisclosureEnergy
import Bilevel.TransportRoundQueryEnergy
import Bilevel.TransportControllerEnergyMeasurable

/-! Energy and the actual ghost failure event of the executed adaptive round
controller. Query insertion, frozen transport, and the legal next-source
disclosure are combined into one derived recurrence on the same trajectory. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportObserver
set_option maxHeartbeats 800000

def roundFactor (n : ℕ) : ℝ := 2*batchFactor n

theorem roundFactor_ge_one (n : ℕ) : 1≤roundFactor n := by
  have hh := batchFactor_ge_one n
  dsimp [roundFactor]
  linarith

def runEnergy {H : Type*} {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) : ℝ :=
  TransportRoundEnergy.total
    (known (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t).2)
    (frame T hT z) (oldFuture T t)

def runFailure {H : Type*} {n D p T : ℕ} (hT : T≤D) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) : Prop :=
  let st := run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t
  TransportRoundQuery.queryPhaseBad T hT a (requests (choose t st)) (known st.2) z ∨
    batchFailure hT t (augment st.2 (choose t st)) z
      (fun e => runPairs hT choose respond (prefixNames n T) (memory,seed T hT z) z e t)

theorem runEnergy_nonneg {H : Type*} {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) : 0≤runEnergy hT choose respond memory z t :=
  TransportRoundEnergy.total_nonneg _ _ _

theorem runEnergy_zero {H : Type*} {n D p T : ℕ} (hT : T≤D) (hpos : 0<T)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) : runEnergy hT choose respond memory z 0=0 := by
  apply seed_ledger_zero T hT hpos z (fun v => v) (oldFuture T 0)
  intro v i hi
  simpa only [oldFuture,Finset.mem_filter,Finset.mem_univ,true_and] using hi

theorem runEnergy_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (memory : H) (t : ℕ) : Measurable (fun z => runEnergy hT choose respond memory z t) :=
  run_blind_energy_measurable T hT choose hc respond hr memory t (oldFuture T t)

theorem run_energy_step {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ)
    (hbudget : batchFactor n*(runEnergy hT choose respond memory z t+(((n+1)*p:ℕ):ℝ)*a)≤(1:ℝ)/4096)
    (hgood : ¬runFailure hT a choose respond memory z t) :
    runEnergy hT choose respond memory z (t+1)≤
      roundFactor n*(runEnergy hT choose respond memory z t+(((n+1)*p:ℕ):ℝ)*a) := by
  let st := run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t
  let g := augment st.2 (choose t st)
  let P := fun e => runPairs hT choose respond (prefixNames n T) (memory,seed T hT z) z e t
  have hg := not_or.mp hgood
  have hq := frozen_query_energy hT a st.2 (choose t st) z (oldFuture T t) hg.1
  have hpair := runPairs_frozen_included hT choose respond (prefixNames n T) (memory,seed T hT z) z
  have hp := frozenAt_prefix hT hn choose respond memory z t
  have hB : batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)≤(1:ℝ)/4096 :=
    (mul_le_mul_of_nonneg_left hq (le_trans (by norm_num) (batchFactor_ge_one n))).trans hbudget
  have hbatch := executed_batch_energy hT hn t g z P
    (fun e => runPairs_supported hT choose respond (prefixNames n T) (memory,seed T hT z) z e t)
    (fun e => (hpair e t).1) (fun e => (hpair e t).2) hp hB hg.2
  have hsmall : TransportRoundEnergy.total (known (execute g z)) (frame T hT z) (postFuture T t)≤(1:ℝ)/4096 :=
    hbatch.trans hB
  have hd := sourceDisclosure_total_energy hT hn t (execute g z) z hsmall
  have hfinal : runEnergy hT choose respond memory z (t+1)≤
      2*TransportRoundEnergy.total (known (execute g z)) (frame T hT z) (postFuture T t) := hd
  apply hfinal.trans
  apply (mul_le_mul_of_nonneg_left hbatch (by norm_num : (0:ℝ)≤2)).trans
  have hh := mul_le_mul_of_nonneg_left hq (le_trans (by norm_num : (0:ℝ)≤1) (roundFactor_ge_one n))
  simpa only [roundFactor,mul_assoc] using hh

end Bilevel.TransportRound
