import Bilevel.EndpointTransportFineLeaves
import Bilevel.ChiCarrierReleaseJets
import Bilevel.ChiLiftedSelection

/-! The actual physical predecessor release is an ordinary framed release
at the last transport endpoint, with the physical full-vector radial radius. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier

def targetNode {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) : Node (Physical n D) where
  n := N.n
  ell := N.ell
  width := N.width
  receiver := N.receiver
  nu := N.nu
  force := N.force
  parentWidth := N.parentWidth
  tailRadius := N.tailRadius
  radius := gamma n*N.radius
  frame := endpointFrame Q N.frame (Fin.last (n+1))

theorem target_coordinates {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (Y : Physical n D) :
    (targetNode Q N).coordinates Y=(physicalCoordinates Q N Y).snd := rfl

theorem physicalRelease_eq_target {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) :
    physicalRelease Q N=(targetNode Q N).release := rfl

theorem physicalRelease_contDiff {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (k : ℕ) :
    ContDiff ℝ k (physicalRelease Q N) := (targetNode Q N).release_contDiff k

theorem physicalRelease_range {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) (Y : Physical n D) :
    0≤physicalRelease Q N Y ∧ physicalRelease Q N Y≤1 := (targetNode Q N).release_range Y

theorem target_admissible {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (hN : NodeJetAdmissible N) : NodeJetAdmissible (targetNode Q N) := by
  have hR : 0≤N.radius := hN.2.1.le.trans hN.2.2.1
  have hRγ : N.radius≤gamma n*N.radius := le_mul_of_one_le_left hR (gamma_range n).1
  exact ⟨hN.1,hN.2.1,hN.2.2.1.trans hRγ,hN.2.2.2.1,hN.2.2.2.2.trans hRγ⟩

theorem physical_release_jets : ∃ C : ℝ,1≤C ∧ ∀ (n D : ℕ) (Q : Rotations n D)
    (N : Node (Block D)),NodeJetAdmissible N → ∀ (Y : Physical n D) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalRelease Q N) Y‖≤C/N.parentWidth^k := by
  obtain ⟨C,hC,hb⟩ := constructed_node_jets
  refine ⟨C,hC,fun n D Q N hN Y k hk => ?_⟩
  have h := target_admissible Q N hN
  exact (hb (Physical n D) (targetNode Q N) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 0 Y k hk).2.2

end Bilevel.EndpointTransportResponse
