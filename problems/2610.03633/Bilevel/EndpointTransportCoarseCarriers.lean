import Bilevel.EndpointTransportSelectedLedger
import Bilevel.EndpointTransportFineFrontier

/-! Actual physical coarse carriers: only the final carrier has its fine
frontier subtracted. The finite sum recovers the exact physical recursion. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def physicalCoarseCarrier {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (t : ℕ) (x : X) : ℝ :=
  physicalCarrier m Q G A B d j I t x-
    if t=d then selectedPhysicalFineFrontier m G A B Q P d j I x else 0

theorem physicalCoarseCarrier_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (t : ℕ) :
    ContDiff ℝ 3 (physicalCoarseCarrier m Q G A B P d j I t) := by
  change ContDiff ℝ 3 (fun x => physicalCarrier m Q G A B d j I t x-
    if t=d then selectedPhysicalFineFrontier m G A B Q P d j I x else 0)
  by_cases ht : t=d
  · simpa only [physicalCoarseCarrier,if_pos ht] using (physicalCarrier_contDiff m Q G A B d j I t).sub
      (selectedPhysicalFineFrontier_contDiff m G A B Q P d j I)
  · simpa only [physicalCoarseCarrier,if_neg ht,sub_zero] using physicalCarrier_contDiff m Q G A B d j I t

theorem physical_coarse_fine_trace {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (x : X) :
    (∑ t : Fin (d+1),physicalCoarseCarrier m Q G A B P d j I t.val x)+
      selectedPhysicalFineFrontier m G A B Q P d j I x=
      physicalRecursive Q G d j I (padded (A x)) (B x) := by
  classical
  have ht (t : Fin (d+1)) : t.val=d ↔ t=Fin.last d := by
    constructor
    · intro h;exact Fin.ext h
    · rintro rfl;rfl
  simp only [physicalCoarseCarrier,Finset.sum_sub_distrib,ht]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,if_true,sub_add_cancel]
  exact (physical_recursive_carrier_trace m Q G A B d j I x).symm

theorem fineScale_le_ledger {N ℓ h : ℝ} (hN : 1≤N) (hℓ : 0≤ℓ) (hh : 0<h)
    (k : ℕ) (hk : k≤3) : fineScale (ℓ*h^2) (ℓ*h) h k≤ledgerScale N ℓ h k := by
  have he : fineScale (ℓ*h^2) (ℓ*h) h k=(ℓ*h^2)/h^k := by
    cases k with
    | zero => simp only [fineScale,pow_zero,div_one]
    | succ k =>
      simp only [fineScale,pow_succ]
      field_simp
      ring
  rw [he]
  exact residualScale_le_ledger hN hℓ hh k hk

end Bilevel.EndpointTransportResponse
