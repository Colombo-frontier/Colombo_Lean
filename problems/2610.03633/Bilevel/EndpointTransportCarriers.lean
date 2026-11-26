import Bilevel.EndpointTransportReleaseCorrection
import Bilevel.EndpointTransportPayloadSize
import Bilevel.ChiLiftedLedger

/-! Actual finite physical carrier decomposition: only the deepest leaf and
the immediately preceding release are replaced by endpoint transport. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def lastParentCarrier {n D : ℕ} (m j : ℕ) (N : Node (Block D))
    (kids : Fin (N.n+1) → Node (Block D)) (A : X →L[ℝ] Blocks m (Block D))
    (B : X →L[ℝ] Physical n D) (Q : Rotations n D) (x : X) : ℝ :=
  jointH m j N (A x)+physicalReleaseCorrection m j N kids A B Q x

theorem lastParentCarrier_contDiff {n D : ℕ} (m j : ℕ) (N : Node (Block D))
    (kids : Fin (N.n+1) → Node (Block D)) (A : X →L[ℝ] Blocks m (Block D))
    (B : X →L[ℝ] Physical n D) (Q : Rotations n D) :
    ContDiff ℝ 3 (lastParentCarrier m j N kids A B Q) :=
  ((jointH_contDiff m j N 3).comp A.contDiff).add (physicalReleaseCorrection_contDiff m j N kids A B Q)

def physicalCarrier {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D) :
    ℕ → ℕ → List ℕ → ℕ → X → ℝ
  | 0,j,I,0,x => physicalPayload Q (G j I) (B x)-(G j I).H 0
  | 0,_,_,_+1,_ => 0
  | d+1,j,I,0,x => if d=0 then
      lastParentCarrier m j (G j I) (fun i => G (j+1) (child I i.val)) A B Q x
      else jointCarrier m G (d+1) j I 0 (A x)
  | d+1,j,I,t+1,x => ∑ i : Fin ((G j I).n+1),ChiLiftedCarrier.selector m j (G j I) A i x*
      physicalCarrier m Q G A B d (j+1) (child I i.val) t x

theorem physicalCarrier_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d j : ℕ) (I : List ℕ) (t : ℕ) : ContDiff ℝ 3 (physicalCarrier m Q G A B d j I t) := by
  induction d generalizing j I t with
  | zero =>
    cases t
    · exact ((physical_payload_contDiff Q (G j I) 3).comp B.contDiff).sub contDiff_const
    · exact contDiff_const
  | succ d ih =>
    cases t with
    | zero =>
      by_cases hd : d=0
      · simpa only [physicalCarrier,if_pos hd] using
          lastParentCarrier_contDiff m j (G j I) (fun i => G (j+1) (child I i.val)) A B Q
      · simpa only [physicalCarrier,if_neg hd] using (jointCarrier_contDiff m G (d+1) j I 0 3).comp A.contDiff
    | succ t =>
      exact ContDiff.sum (fun i _ => (ChiLiftedCarrier.selector_contDiff m j (G j I) A i 3).mul
        (ih (j+1) (child I i.val) t))

theorem physical_carrier_local_formula {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d j : ℕ) (I : List ℕ) (x : X) :
    physicalCarrier m Q G A B (d+1) j I 0 x=
      (G j I).H (block m j (A x))-(∑ i : Fin ((G j I).n+1),(G j I).residual i (block m j (A x)))+
      ∑ i : Fin ((G j I).n+1),(G j I).residual i (block m j (A x))*
        (if d=0 then physicalRelease Q (G (j+1) (child I i.val)) (B x)
          else (G (j+1) (child I i.val)).release (block m (j+1) (A x))) := by
  by_cases hd : d=0
  · simp only [physicalCarrier,if_pos hd,lastParentCarrier,physicalReleaseCorrection,jointH,jointResidual,
      Function.comp_apply,mul_sub,mul_one,Finset.sum_sub_distrib]
    ring
  · simp only [physicalCarrier,if_neg hd,jointCarrier,selectedCarrier,padded]

theorem physical_recursive_carrier_trace {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d j : ℕ) (I : List ℕ) (x : X) :
    physicalRecursive Q G d j I (padded (A x)) (B x)=
      ∑ t : Fin (d+1),physicalCarrier m Q G A B d j I t.val x := by
  induction d generalizing j I with
  | zero => simp [physicalRecursive,physicalCarrier]
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_succ,Fin.val_zero]
    rw [physical_carrier_local_formula]
    simp only [physicalCarrier,physicalRecursive]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum,← ih]
    rfl

end Bilevel.EndpointTransportResponse
