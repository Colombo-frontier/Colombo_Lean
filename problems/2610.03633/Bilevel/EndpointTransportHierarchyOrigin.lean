import Bilevel.EndpointTransportNormalExtension
import Bilevel.EndpointTransportHybridSource
import Bilevel.ChiHybridExtension

/-! Exact zero lower initialization for the actual physical hierarchy. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem physicalRelease_zero {n D : ℕ} (Q : Rotations n D) (N : Node (Block D)) :
    physicalRelease Q N 0=0 := by
  have h := physical_release_response 1 1 Q N 0
  simpa only [physicalResponse_zero,smul_zero,Node.release_zero] using h

theorem physicalCarrier_zero {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d j : ℕ) (I : List ℕ) (t : ℕ) : physicalCarrier m Q G A B d j I t 0=0 := by
  induction d generalizing j I t with
  | zero => cases t <;> simp [physicalCarrier,physical_payload_zero]
  | succ d ih =>
    cases t with
    | zero =>
      rw [physical_carrier_local_formula]
      simp only [map_zero,physicalRelease_zero,Node.release_zero,ite_self,mul_zero,
        Finset.sum_const_zero,add_zero,Node.H_zero_eq_residual_sum,sub_self]
    | succ t => simp only [physicalCarrier,ih,mul_zero,Finset.sum_const_zero]

theorem physicalFineFrontier_zero {n D : ℕ} (Q : Rotations n D) (N : Node (Block D))
    (P : ChiFine.Parameters) : physicalFineFrontier Q N P 0=0 := by
  have h := physical_fine_frontier_response 1 1 Q N P 0
  simpa [physicalResponse_zero,ChiFine.frontier,ZeroChainResidualScaled.scaled,
    Node.coordinates_zero,centeredResidual_zero] using h

theorem selectedPhysicalFineFrontier_zero {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) :
    selectedPhysicalFineFrontier m G A B Q P d j I 0=0 := by
  induction d generalizing j I with
  | zero => simp [selectedPhysicalFineFrontier,ChiLiftedCarrier.selectFamily,physicalFineFrontier_zero]
  | succ d ih =>
    change (∑ i : Fin ((G j I).n+1),ChiLiftedCarrier.selector m j (G j I) A i 0*
      selectedPhysicalFineFrontier m G A B Q P d (j+1) (child I i.val) 0)=0
    simp only [ih,mul_zero,Finset.sum_const_zero]

theorem physicalHierarchyCoarse_zero {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J : ℕ) (i : Fin J) :
    physicalHierarchyCoarse Q M G P J i 0=0 := by
  simp [physicalHierarchyCoarse,outerPhysicalCoarseFamily,outerPhysicalCoarseCarrier,
    outerPhysicalCarrier,outerPhysicalFineFrontier,macroSelected,physicalCarrier_zero,
    selectedPhysicalFineFrontier_zero]

theorem physicalHierarchyFine_zero {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J : ℕ) :
    (physicalHierarchyFine Q M G P J).r 0=0 := by
  simp [physicalHierarchyFine,outerPhysicalFineData,outerPhysicalFineFrontier,macroSelected,
    selectedPhysicalFineFrontier_zero]

theorem physicalHierarchy_normal_origin {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (hw : ∀ i : Fin J,0<(G (i.val+1) []).width) (hR : ∀ i : Fin J,0<R (i.val+1)) :
    gradient (fun q : Normals s =>
      physicalHierarchyExtension Q M G P J s index radialIndex fineIndex ρ R dn (pack 0 q)) 0=0 := by
  unfold physicalHierarchyExtension
  rw [(total_normal_gradient index (physicalHierarchyCoarse Q M G P J)
    (fun i => ChiOuter.coarseWidth G (i.val+1)) (fun i => ChiOuter.coarseWidth_pos G _ (hw i))
    fineIndex (physicalHierarchyFine Q M G P J) (1/dn) radialIndex
    (publicRadialProjection (E:=E) n D) (publicRadialProjection_norm_le (E:=E) n D)
    (publicRadialCurvature n ρ) (publicRadialRadius n R) dn (publicRadialRadius_pos n R hR) 0).gradient]
  simp [physicalHierarchyCoarse_zero,physicalHierarchyFine_zero]
  simp [EuclideanSpace.single]

theorem physicalHierarchy_response_origin {D : ℕ} (L κ : ℝ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (hw : ∀ i : Fin J,0<(G (i.val+1) []).width) (hR : ∀ i : Fin J,0<R (i.val+1)) :
    ChiHybrid.responseOfExtension
      (physicalExtension (physicalHierarchyExtension Q M G P J s index radialIndex fineIndex ρ R dn))
      (sourceHybridTangent (U:=Blocks J (Block D)) L κ Q) 0=0 := by
  unfold ChiHybrid.responseOfExtension
  rw [sourceHybridTangent_zero,physicalExtension_normal_gradient
    (physicalHierarchyExtension_contDiff Q M G P J s index radialIndex fineIndex ρ R dn hw)]
  change pack 0 (gradient (fun q : Normals s =>
    physicalHierarchyExtension Q M G P J s index radialIndex fineIndex ρ R dn (pack 0 q)) 0)=0
  rw [physicalHierarchy_normal_origin Q M G P J s index radialIndex fineIndex ρ R dn hw hR]
  rfl

end Bilevel.EndpointTransportResponse
