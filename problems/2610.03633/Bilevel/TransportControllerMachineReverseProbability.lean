import Bilevel.TransportControllerMachineReverseCheck
import Bilevel.TransportControllerMachineForwardProbability

/-! Actual-run reverse-angle probability bound under the same original
network law as the forward bound. It uses the proved inverse-edge posterior
and the real current forward responses, not independent edge directions. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian TransportNetwork TransportNetworkAuxiliary TransportRound TransportControllerEdge
set_option maxHeartbeats 800000

theorem actual_reverse_failure_probability {n D T p k : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (t r : ℕ) (hrpos : 0<r)
    (hD : T+(1+((TransportRound.size n p 1 1 t+p)+historyProbes n p 1 1 t))+r≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k)) {s |
      reverseMonitor hT t
        (frozenAt hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 t) s.2.1
        (fun f => runPairs hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 f t)
        (forwardLedger (frozenAt hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 t) s.2.1
          (known (postGrant T hT t (frozenAt hT choose respond (prefixNames n T)
            (s.1,seed T hT s.2.1) s.2.1 t) s.2.1))) e} ≤
      ((1+((TransportRound.size n p 1 1 t+p)+historyProbes n p 1 1 t) : ℕ):ℝ≥0∞)*
        budget (reverseDimension n (TransportRound.size n p 1 1 t+p)) r := by
  have hp := randomized_network_inverse_machine_angle_failure hT e
    (reverseProgram (k := T) H e choose hc respond hr (prefixNames n T) t)
    (initialMemory (k := k) H e) (initialMemory_measurable H e) ρ r hrpos hD
  apply le_trans (measure_mono ?_) hp
  intro s hs
  change failure (reverseProgram H e choose hc respond hr (prefixNames n T) t)
    (swapState ((context T hT e s.2.1,(s.1,seed T hT s.2.1)),frameStore e (context T hT e s.2.1))) (s.2.1.2 e)⁻¹
  exact reverseProgram_failure_of_actual H hT e choose hc respond hr (prefixNames n T)
    (s.1,seed T hT s.2.1) s.2.1 t hs

end Bilevel.TransportControllerMachine
