import Bilevel.EndpointTransportReadout
import Bilevel.ChiSplitPayload
import Bilevel.ChiRecursivePayload

/-! Actual physical leaf payload, gates and receivers, and exact substitution
through every recursive ancestor. No restriction to the hidden frame is used. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive PrimitiveGeometry RadialWrapper

def physicalCoordinates {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (Y : Physical n D) : ChiSplitChain.Latent N.n :=
  ChiSplitChain.readout (sourceReadout Q N.frame) (targetReadout Q N.frame)
    (compress (gamma n*N.radius) Y)

def physicalPayload {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (Y : Physical n D) : ℝ :=
  ChiSplitChain.payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    (physicalCoordinates Q N Y)

def physicalRelease {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (Y : Physical n D) : ℝ := releaseGate ((physicalCoordinates Q N Y).snd (Fin.last N.n)/N.parentWidth)

def physicalSelector {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (i : Fin (N.n+1)) (Y : Physical n D) : ℝ :=
  selector N.n i (N.width⁻¹ • (physicalCoordinates Q N Y).snd)

def physicalResidual {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (i : Fin (N.n+1)) (Y : Physical n D) : ℝ :=
  ChiSplitChain.residualTerm N.n N.ell N.width i (physicalCoordinates Q N Y)

theorem physical_coordinates_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (N : Node (Block D)) (v : Block D) :
    physicalCoordinates Q N (physicalResponse δ c Q v)=
      pack (N.coordinates (gain n δ c • v)) (N.coordinates (gain n δ c • v)) := by
  unfold physicalCoordinates
  rw [ChiSplitChain.readout_apply,(readout_response δ c N.radius Q N.frame v).1,
    (readout_response δ c N.radius Q N.frame v).2]
  rfl

theorem physical_payload_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (N : Node (Block D)) (v : Block D) :
    physicalPayload Q N (physicalResponse δ c Q v)=N.H (gain n δ c • v) := by
  unfold physicalPayload
  rw [physical_coordinates_response,ChiSplitChain.payload_diagonal]
  rfl

theorem physical_payload_zero {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) :
    physicalPayload Q N 0=N.H 0 := by
  have hh := physical_payload_response 1 1 Q N 0
  simpa only [physicalResponse_zero,smul_zero] using hh

theorem physical_release_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (N : Node (Block D)) (v : Block D) :
    physicalRelease Q N (physicalResponse δ c Q v)=N.release (gain n δ c • v) := by
  unfold physicalRelease
  rw [physical_coordinates_response]
  rfl

theorem physical_selector_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (N : Node (Block D)) (i : Fin (N.n+1)) (v : Block D) :
    physicalSelector Q N i (physicalResponse δ c Q v)=N.selector i (gain n δ c • v) := by
  unfold physicalSelector
  rw [physical_coordinates_response]
  rfl

theorem physical_residual_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (N : Node (Block D)) (i : Fin (N.n+1)) (v : Block D) :
    physicalResidual Q N i (physicalResponse δ c Q v)=N.residual i (gain n δ c • v) := by
  unfold physicalResidual
  rw [physical_coordinates_response,ChiSplitChain.residualTerm_diagonal]
  rfl

def physicalRecursive {n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D)) :
    ℕ → ℕ → List ℕ → (ℕ → Block D) → Physical n D → ℝ
  | 0,j,I,_u,Y => physicalPayload Q (G j I) Y-(G j I).H 0
  | d+1,j,I,u,Y =>
      (G j I).H (u j)-(∑ i : Fin ((G j I).n+1),(G j I).residual i (u j))+
      (∑ i : Fin ((G j I).n+1),(G j I).residual i (u j)*
        (if d=0 then physicalRelease Q (G (j+1) (child I i.val)) Y
          else (G (j+1) (child I i.val)).release (u (j+1))))+
      ∑ i : Fin ((G j I).n+1),(G j I).selector i (u j)*physicalRecursive Q G d (j+1) (child I i.val) u Y

theorem physical_recursive_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (G : Geometry (Block D)) (d j : ℕ) (I : List ℕ) (u : ℕ → Block D) (v : Block D)
    (hlast : u (j+d)=gain n δ c • v) :
    physicalRecursive Q G d j I u (physicalResponse δ c Q v)=payloadValue G d j I u := by
  induction d generalizing j I with
  | zero =>
    simp only [Nat.add_zero] at hlast
    simp only [physicalRecursive,payloadValue,physical_payload_response,hlast]
  | succ d ih =>
    have hr (i : Fin ((G j I).n+1)) :
        (if d=0 then physicalRelease Q (G (j+1) (child I i.val)) (physicalResponse δ c Q v)
          else (G (j+1) (child I i.val)).release (u (j+1)))=
        (G (j+1) (child I i.val)).release (u (j+1)) := by
      by_cases hd : d=0
      · subst d
        rw [if_pos rfl,physical_release_response]
        rw [show u (j+1)=gain n δ c • v from hlast]
      · rw [if_neg hd]
    have hc (i : Fin ((G j I).n+1)) := ih (j+1) (child I i.val) (by
      rw [show j+1+d=j+(d+1) by omega]
      exact hlast)
    simp only [physicalRecursive,payloadValue,hr,hc]

end Bilevel.EndpointTransportResponse
