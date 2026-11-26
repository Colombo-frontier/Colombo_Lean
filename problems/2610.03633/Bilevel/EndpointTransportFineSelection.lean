import Bilevel.EndpointTransportFineLeaves
import Bilevel.ChiFineCompositionActive

/-! Actual physical fine pieces selected through all ordinary ancestors.
The ambient product may be heterogeneous; both projections are explicit. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def selectedPhysicalFinePiece {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (p d j : ℕ) (I : List ℕ) : X → ℝ :=
  ChiLiftedCarrier.selectFamily m G A (fun k I => physicalFinePiece Q (G k I) P p ∘ B) d j I

def selectedPhysicalFineFrontier {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) : X → ℝ :=
  ChiLiftedCarrier.selectFamily m G A (fun k I => physicalFineFrontier Q (G k I) P ∘ B) d j I

theorem selectedPhysicalFinePiece_contDiff {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (p d j : ℕ) (I : List ℕ) :
    ContDiff ℝ 3 (selectedPhysicalFinePiece m G A B Q P p d j I) :=
  ChiLiftedCarrier.selectFamily_contDiff m G A _
    (fun k I => (physicalFinePiece_contDiff Q (G k I) P p).comp B.contDiff) d j I

theorem selectedPhysicalFineFrontier_contDiff {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) :
    ContDiff ℝ 3 (selectedPhysicalFineFrontier m G A B Q P d j I) :=
  ChiLiftedCarrier.selectFamily_contDiff m G A _
    (fun k I => (physicalFineFrontier_contDiff Q (G k I) P).comp B.contDiff) d j I

theorem selected_physical_fine_decomposition {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (x : X) :
    (∑ p ∈ Finset.range (levels P.θ+1),selectedPhysicalFinePiece m G A B Q P p d j I x)=
      selectedPhysicalFineFrontier m G A B Q P d j I x := by
  rw [← Fin.sum_univ_eq_sum_range (fun p => selectedPhysicalFinePiece m G A B Q P p d j I x)]
  unfold selectedPhysicalFinePiece selectedPhysicalFineFrontier
  rw [← ChiLiftedCarrier.selectFamily_sum]
  have he : (fun k I x => ∑ p : Fin (levels P.θ+1),(physicalFinePiece Q (G k I) P p.val ∘ B) x)=
      (fun k I => physicalFineFrontier Q (G k I) P ∘ B) := by
    funext k I x
    simp only [Function.comp_apply]
    rw [Fin.sum_univ_eq_sum_range (fun p => physicalFinePiece Q (G k I) P p (B x)) (levels P.θ+1)]
    exact physical_fine_decomposition Q (G k I) P (B x)
  rw [he]

theorem selected_physical_fine_overlap {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (x : X) :
    (ChiLiftedCarrier.activeLeaves (levels P.θ)
      (fun p => selectedPhysicalFinePiece m G A B Q P p d j I) x).card≤3 := by
  apply ChiLiftedCarrier.selected_overlap m G A
    (fun p k I => physicalFinePiece Q (G k I) P p ∘ B)
    (fun p k I => (physicalFinePiece_contDiff Q (G k I) P p).comp B.contDiff) _ 3 d j I x
  intro k I
  exact ChiLiftedCarrier.split_composed_overlap (G k I).n P (physicalCoordinates Q (G k I) ∘ B)
    ((physicalCoordinates_contDiff Q (G k I)).comp B.contDiff) x

end Bilevel.EndpointTransportResponse
