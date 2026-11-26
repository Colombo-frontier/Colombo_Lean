import Bilevel.TransportHierarchyFrame
import Bilevel.TransportRoundPrefixReadout

/-! Actual endpoint prefix arrays are read from the finite network store.
The source is one global terminal coordinate ahead of the target; the
comparison uses the source hierarchy counter, including canonical all-list
lookup, not a separate next column at every closed future node. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open ChiTreeProgress ChiHierarchyIndex ChiBoundedChain TransportRound TransportNetwork
  EndpointTransportResponse EuclideanGaussian
set_option maxHeartbeats 700000
open Classical

def terminalReadout {n D : ℕ} (counts : ℕ → ℕ) (J p t : ℕ)
    (g : Generators (n+1) D (size (n+1) p 1 1 t))
    (v : EndpointTransportMatrix.Index n) (I : List ℕ) (k : Fin (counts (J+1)+1)) : EuclideanGaussian.Space D :=
  prefixReadout (Nat.succ_pos n) p t g v (canonicalTerminalIndex counts (J+1) I k)

theorem terminalReadout_measurable {n D : ℕ} (counts : ℕ → ℕ) (J p t : ℕ)
    (v : EndpointTransportMatrix.Index n) :
    Measurable (fun g => terminalReadout (n:=n) (D:=D) counts J p t g v) := by
  apply measurable_pi_lambda
  intro I
  apply measurable_pi_lambda
  intro k
  exact (measurable_pi_apply (canonicalTerminalIndex counts (J+1) I k)).comp
    ((measurable_pi_apply v).comp (prefixReadout_measurable (Nat.succ_pos n) p t))

theorem canonical_source_protected {n : ℕ} (counts : ℕ → ℕ) (J t : ℕ)
    (I : List ℕ) (k : Fin (counts (J+1)+1)) :
    Protected t (0 : Vertex (n+1)) (canonicalTerminalIndex counts (J+1) I k) ↔
      k.val<canonicalCounter counts J (t/(n+1)+1) J I := by
  rw [canonical_terminal_prefix]
  change (canonicalTerminalIndex counts (J+1) I k).val*(n+1)+0≤t ↔ _
  rw [Nat.add_zero,←Nat.le_div_iff_mul_le (Nat.succ_pos n)]
  change (canonicalTerminalIndex counts (J+1) I k).val≤t/(n+1) ↔
    (canonicalTerminalIndex counts (J+1) I k).val<t/(n+1)+1
  omega

theorem canonical_target_protected {n : ℕ} (counts : ℕ → ℕ) (J t : ℕ)
    (I : List ℕ) (k : Fin (counts (J+1)+1)) :
    Protected t (Fin.last (n+1)) (canonicalTerminalIndex counts (J+1) I k) ↔
      k.val<canonicalCounter counts J (t/(n+1)) J I := by
  rw [completed_prefix (Nat.succ_pos n),canonical_terminal_prefix]
  change (canonicalTerminalIndex counts (J+1) I k).val+1≤t/(n+1) ↔
    (canonicalTerminalIndex counts (J+1) I k).val<t/(n+1)
  omega

theorem terminalSourceReadout_actual {H : Type*} {n D p : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (hD : capacity counts (J+1) 0≤D)
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p (capacity counts (J+1) 0) → H)
    (memory : H) (z : Latent (n+1) D) (t : ℕ) (I : List ℕ) (k : Fin (counts (J+1)+1)) :
    terminalReadout counts J p t
      (run (capacity counts (J+1) 0) hD choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
        (memory,seed (capacity counts (J+1) 0) hD z) z t).2 0 I k =
      if k.val<canonicalCounter counts J (t/(n+1)+1) J I then
        physicalRotations z 0 (canonicalTerminalFrame counts (J+1) hD z I (basis k)) else 0 := by
  rw [terminalReadout,prefixReadout_actual]
  rw [canonical_source_protected,canonical_terminal_network_column]
  split_ifs <;> rfl

theorem terminalTargetReadout_actual {H : Type*} {n D p : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (hD : capacity counts (J+1) 0≤D)
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p (capacity counts (J+1) 0) → H)
    (memory : H) (z : Latent (n+1) D) (t : ℕ) (I : List ℕ) (k : Fin (counts (J+1)+1)) :
    terminalReadout counts J p t
      (run (capacity counts (J+1) 0) hD choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
        (memory,seed (capacity counts (J+1) 0) hD z) z t).2 (Fin.last (n+1)) I k =
      if k.val<canonicalCounter counts J (t/(n+1)) J I then
        physicalRotations z (Fin.last (n+1)) (canonicalTerminalFrame counts (J+1) hD z I (basis k)) else 0 := by
  rw [terminalReadout,prefixReadout_actual]
  rw [canonical_target_protected,canonical_terminal_network_column]
  split_ifs <;> rfl

end Bilevel.TransportHierarchy

