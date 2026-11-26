import Bilevel.TransportHierarchyReachableColumns
import Bilevel.EndpointTransportReadout

/-! The actual physical endpoint arrays are obtained by inserting the
literal finite network-store readouts into their physical endpoint layer.
No hidden orientation or undisclosed frame is used by this evaluator. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiTreeProgress ChiHierarchyIndex ChiBoundedChain TransportRound TransportNetwork
  EndpointTransportResponse ChiCarrier
set_option maxHeartbeats 700000

def endpointReadout {n D : ℕ} (counts : ℕ → ℕ) (J p t : ℕ)
    (g : Generators (n+1) D (size (n+1) p 1 1 t))
    (v : EndpointTransportMatrix.Index n) (I : List ℕ) (k : Fin (counts (J+1)+1)) : Physical n D :=
  insertion (n+2) v (terminalReadout counts J p t g v I k)

theorem endpointReadout_measurable {n D : ℕ}
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    (counts : ℕ → ℕ) (J p t : ℕ) (v : EndpointTransportMatrix.Index n) :
    Measurable (fun g => endpointReadout (n:=n) (D:=D) counts J p t g v) := by
  apply measurable_pi_lambda
  intro I
  apply measurable_pi_lambda
  intro k
  exact (insertion (n+2) v).continuous.measurable.comp
    ((measurable_pi_apply k).comp ((measurable_pi_apply I).comp
      (terminalReadout_measurable counts J p t v)))

variable {H : Type*} {n D p : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (hD : capacity counts (J+1) 0≤D)
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p (capacity counts (J+1) 0) → H)
    (memory : H) (z : Latent (n+1) D)

theorem endpointSourceReadout_prefix (t : ℕ) (I : List ℕ) (k : Fin (counts (J+1)+1))
    (hk : k.val<canonicalCounter counts J (t/(n+1)+1) J I) :
    endpointReadout counts J p t
      (run (capacity counts (J+1) 0) hD choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
        (memory,seed (capacity counts (J+1) 0) hD z) z t).2 0 I k =
      endpointFrame (physicalRotations z) (canonicalTerminalFrame counts (J+1) hD z I) 0 (basis k) := by
  unfold endpointReadout
  rw [terminalSourceReadout_actual counts J hD choose respond memory z t I k,if_pos hk]
  rfl

theorem endpointTargetReadout_prefix (t : ℕ) (I : List ℕ) (k : Fin (counts (J+1)+1))
    (hk : k.val<canonicalCounter counts J (t/(n+1)) J I) :
    endpointReadout counts J p t
      (run (capacity counts (J+1) 0) hD choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
        (memory,seed (capacity counts (J+1) 0) hD z) z t).2 (Fin.last (n+1)) I k =
      endpointFrame (physicalRotations z) (canonicalTerminalFrame counts (J+1) hD z I)
        (Fin.last (n+1)) (basis k) := by
  unfold endpointReadout
  rw [terminalTargetReadout_actual counts J hD choose respond memory z t I k,if_pos hk]
  rfl

end Bilevel.TransportHierarchy
