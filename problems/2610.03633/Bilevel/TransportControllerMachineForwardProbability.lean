import Bilevel.TransportControllerMachineForwardCheck
import Bilevel.TransportControllerMachineNetwork
import Bilevel.TransportRoundRunMeasurable

/-! A concrete actual-run forward-angle probability bound. The Borel policy,
paired-domain legality, and equality of the terminal ghost check with the
real frozen-run monitor are all discharged. Private randomness is integrated
under its explicitly independent product with the original instance law. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian TransportNetwork TransportNetworkAuxiliary TransportRound TransportControllerEdge
set_option maxHeartbeats 800000

def contextSeed {n D T : ℕ} {e : Edge n} (c : Context (d := D) e T) : Generators n D 1 := fun v _ =>
  if v=0 then if h : 0<T then c.1 0 ⟨0,h⟩ else 0 else 0

theorem contextSeed_measurable {n D T : ℕ} (e : Edge n) : Measurable (contextSeed (D := D) (T := T) (e := e)) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  by_cases hv : v=0
  · subst v
    by_cases h : 0<T
    · simp only [contextSeed,ite_true,dif_pos h]
      exact (measurable_pi_apply (⟨0,h⟩ : Fin T)).comp ((measurable_pi_apply (0 : Vertex n)).comp measurable_fst)
    · simp only [contextSeed,ite_true,dif_neg h]
      exact measurable_const
  · simp only [contextSeed,if_neg hv]
    exact measurable_const

theorem contextSeed_correct {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) :
    contextSeed (context T hT e z)=seed T hT z := rfl

def initialMemory {n D T k : ℕ} (H : Memory.{u}) (e : Edge n)
    (p : H × FullContext (D := D) e T k) : RoundMemory H D T 1 e :=
  (p.2.1,(p.1,contextSeed p.2.1))

theorem initialMemory_measurable {n D T k : ℕ} (H : Memory.{u}) (e : Edge n) :
    Measurable (initialMemory (D := D) (T := T) (k := k) H e) :=
  (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk ((contextSeed_measurable e).comp (measurable_fst.comp measurable_snd)))

theorem actual_forward_failure_probability {n D T p k : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (t r : ℕ) (hrpos : 0<r)
    (hD : T+(1+historyProbes n p 1 1 t)+r≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k)) {s |
      forwardMonitor hT t
        (frozenAt hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 t) s.2.1
        (fun f => runPairs hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 f t)
        (known (postGrant T hT t (frozenAt hT choose respond (prefixNames n T)
          (s.1,seed T hT s.2.1) s.2.1 t) s.2.1)) e} ≤
      ((1+historyProbes n p 1 1 t : ℕ):ℝ≥0∞)*budget ((TransportRound.size n p 1 1 t+p)+1) r := by
  have hb := randomized_network_machine_angle_failure hT e
    (forwardProgram (k := T) H e choose hc respond hr (prefixNames n T) t)
    (initialMemory (k := k) H e) (initialMemory_measurable H e) ρ r hrpos hD
  convert hb using 1
  congr 1
  ext s
  change _ ↔ failure (forwardProgram H e choose hc respond hr (prefixNames n T) t)
    ((context T hT e s.2.1,(s.1,seed T hT s.2.1)),frameStore e (context T hT e s.2.1)) (s.2.1.2 e)
  exact (forwardProgram_failure H hT e choose hc respond hr (prefixNames n T)
    (s.1,seed T hT s.2.1) s.2.1 t).symm

end Bilevel.TransportControllerMachine
