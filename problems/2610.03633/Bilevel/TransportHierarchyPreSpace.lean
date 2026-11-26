import Bilevel.TransportHierarchyPrefixReadout
import Bilevel.TransportRoundFrozenProjection

/-! Source-specific physical endpoint certificates in the PREBATCH
query-augmented space. The nonlinear inverse can use this space while the
quadratic Hessian action is evaluated separately from the frozen batch. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiTreeProgress ChiHierarchyIndex ChiBoundedChain TransportRound TransportNetwork
  EndpointTransportResponse ProjectionGeometry
set_option maxHeartbeats 600000

variable {H : Type*} {n D p : ℕ} (counts : ℕ → ℕ) (J : ℕ)
    (hD : capacity counts (J+1) 0≤D)
    (choose : ∀ t,H × Generators (n+1) D (size (n+1) p 1 1 t) → Queries (n+1) D p)
    (respond : ∀ t,StepData H (n+1) D (size (n+1) p 1 1 t) p (capacity counts (J+1) 0) → H)
    (memory : H) (z : Latent (n+1) D)

def terminalPreSpace (t : ℕ) : Known (n+1) D :=
  known (frozenAt hD choose respond (prefixNames (n+1) (capacity counts (J+1) 0))
    (memory,seed (capacity counts (J+1) 0) hD z) z t)

theorem terminalPreSpace_keeps (t : ℕ) (v : Vertex (n+1)) :
    known (run (capacity counts (J+1) 0) hD choose respond
      (prefixNames (n+1) (capacity counts (J+1) 0))
      (memory,seed (capacity counts (J+1) 0) hD z) z t).2 v ≤
      terminalPreSpace counts J hD choose respond memory z t v := by
  unfold terminalPreSpace frozenAt
  rw [augment_span]
  exact le_sup_left

theorem terminalPreSpace_query (t : ℕ) (v : Vertex (n+1)) (a : Fin p) :
    choose t (run (capacity counts (J+1) 0) hD choose respond
      (prefixNames (n+1) (capacity counts (J+1) 0))
      (memory,seed (capacity counts (J+1) 0) hD z) z t) v a ∈
      terminalPreSpace counts J hD choose respond memory z t v := by
  unfold terminalPreSpace frozenAt
  rw [augment_span]
  exact (show TransportGeneratorStore.span _ ≤ _ from le_sup_right)
    (TransportGeneratorStore.generator_mem _ a)

theorem terminalSource_mem_preSpace (t : ℕ) (I : List ℕ) (k : Fin (counts (J+1)+1))
    (hk : k.val<canonicalCounter counts J (t/(n+1)+1) J I) :
    physicalRotations z 0 (canonicalTerminalFrame counts (J+1) hD z I (basis k)) ∈
      terminalPreSpace counts J hD choose respond memory z t 0 := by
  rw [canonical_terminal_network_column]
  apply terminalPreSpace_keeps counts J hD choose respond memory z t 0
  apply run_prefix (capacity counts (J+1) 0) hD (Nat.succ_pos n) choose respond memory z t
  exact (canonical_source_protected counts J t I k).mpr hk

theorem terminalTarget_mem_preSpace (t : ℕ) (I : List ℕ) (k : Fin (counts (J+1)+1))
    (hk : k.val<canonicalCounter counts J (t/(n+1)) J I) :
    physicalRotations z (Fin.last (n+1)) (canonicalTerminalFrame counts (J+1) hD z I (basis k)) ∈
      terminalPreSpace counts J hD choose respond memory z t (Fin.last (n+1)) := by
  rw [canonical_terminal_network_column]
  apply terminalPreSpace_keeps counts J hD choose respond memory z t (Fin.last (n+1))
  apply run_prefix (capacity counts (J+1) 0) hD (Nat.succ_pos n) choose respond memory z t
  exact (canonical_target_protected counts J t I k).mpr hk

theorem terminalTarget_projection (M : ℕ) (b : ℝ)
    (hg : ProjectionGood hD choose respond M b memory z)
    (t : ℕ) (ht : t<M) (I : List ℕ) (k : Fin (counts (J+1)+1))
    (hk : canonicalCounter counts J (t/(n+1)) J I≤k.val) :
    ‖(terminalPreSpace counts J hD choose respond memory z t (Fin.last (n+1))).orthogonalProjection
      (physicalRotations z (Fin.last (n+1)) (canonicalTerminalFrame counts (J+1) hD z I (basis k)))‖≤b := by
  have hp : ¬Protected t (Fin.last (n+1)) (canonicalTerminalIndex counts (J+1) I k) := by
    rw [canonical_target_protected]
    omega
  have hh := hg.2 t ht (Fin.last (n+1)) (canonicalTerminalIndex counts (J+1) I k) hp
  rw [←canonical_terminal_network_column counts (J+1) hD z I (Fin.last (n+1)) k] at hh
  exact hh

theorem terminalTarget_width_margin (M : ℕ) (b : ℝ)
    (hg : ProjectionGood hD choose respond M b memory z)
    (t : ℕ) (ht : t<M) (I : List ℕ) (k : Fin (counts (J+1)+1))
    (hk : canonicalCounter counts J (t/(n+1)) J I≤k.val)
    (radius width : ℝ) (hr : 0≤radius) (hbudget : (EndpointTransportMatrix.gamma n*radius)*b≤width/8) :
    (EndpointTransportMatrix.gamma n*radius)*
      ‖(terminalPreSpace counts J hD choose respond memory z t (Fin.last (n+1))).orthogonalProjection
        (physicalRotations z (Fin.last (n+1)) (canonicalTerminalFrame counts (J+1) hD z I (basis k)))‖≤width/8 :=
  (mul_le_mul_of_nonneg_left
    (terminalTarget_projection counts J hD choose respond memory z M b hg t ht I k hk)
    (mul_nonneg (gamma_positive n).le hr)).trans hbudget

end Bilevel.TransportHierarchy
