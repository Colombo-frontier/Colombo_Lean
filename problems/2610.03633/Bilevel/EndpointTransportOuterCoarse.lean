import Bilevel.EndpointTransportOuterCarriers
import Bilevel.EndpointTransportOuterFine

/-! Actual outer coarse carriers retain every physical carrier except for
the fine frontier subtracted once, at the final level. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open ChiRecursive ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def outerPhysicalCoarseCarrier {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d t : ℕ) (x : X) : ℝ :=
  outerPhysicalCarrier m Q M macroP G A B d t x-
    if t=d then outerPhysicalFineFrontier m Q M macroP G A B P d x else 0

def outerPhysicalCoarseFamily {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (J : ℕ) (i : Fin J) : X → ℝ :=
  outerPhysicalCoarseCarrier m Q M macroP G A B P J (i.val+1)

theorem outerPhysicalCoarseCarrier_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d t : ℕ) : ContDiff ℝ 3 (outerPhysicalCoarseCarrier m Q M macroP G A B P d t) := by
  unfold outerPhysicalCoarseCarrier
  split_ifs
  · exact (outerPhysicalCarrier_contDiff m Q M macroP G A B d t).sub
      (outerPhysicalFineFrontier_contDiff m Q M macroP G A B P d)
  · exact (outerPhysicalCarrier_contDiff m Q M macroP G A B d t).sub contDiff_const

theorem outerPhysicalCoarseFamily_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (J : ℕ) (i : Fin J) : ContDiff ℝ 3 (outerPhysicalCoarseFamily m Q M macroP G A B P J i) :=
  outerPhysicalCoarseCarrier_contDiff m Q M macroP G A B P J (i.val+1)

theorem outer_physical_coarse_fine_trace {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (j : ℕ) (x : X) :
    (∑ i : Fin (j+1),outerPhysicalCoarseFamily m Q M macroP G A B P (j+1) i x)+
      outerPhysicalFineFrontier m Q M macroP G A B P (j+1) x=
      ∑ i : Fin (j+1),outerPhysicalCarrier m Q M macroP G A B (j+1) (i.val+1) x := by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  have hi (i : Fin j) : i.castSucc.val+1≠j+1 := by change i.val+1≠j+1;omega
  simp only [outerPhysicalCoarseFamily,outerPhysicalCoarseCarrier,hi,if_false,sub_zero,Fin.val_last,if_pos rfl,if_true]
  ring

end Bilevel.EndpointTransportResponse
