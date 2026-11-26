import Bilevel.EndpointTransportOuterCoarse
import Bilevel.EndpointTransportOuterFineCoupling
import Bilevel.EndpointTransportRadialChannels
import Bilevel.EndpointTransportNormalSpace
import Bilevel.ChiOuterExtensionTrace

/-! The complete actual physical normal extension on its heterogeneous
tangent space. The compact coarse and fine terms share exactly the public
normal readout, with the physically rescaled final radial channel. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiRecursive ChiCarrier ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def physicalHierarchyCoarse {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J : ℕ) : Fin J → PhysicalBase E J n D → ℝ :=
  outerPhysicalCoarseFamily J Q M (baseMacroProjection J n D) G
    (baseOrdinaryProjection J n D) (basePhysicalProjection J n D) P J

def physicalHierarchyFine {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J : ℕ) : CompensatedMean.Data (E:=PhysicalBase E J n D) :=
  outerPhysicalFineData J Q M (baseMacroProjection J n D) G
    (baseOrdinaryProjection J n D) (basePhysicalProjection J n D) P J

def physicalHierarchyExtension {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J s : ℕ)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) : Full (PhysicalBase E J n D) s → ℝ :=
  total coarseIndex (physicalHierarchyCoarse Q M G P J) (fun i => ChiOuter.coarseWidth G (i.val+1))
    fineIndex (physicalHierarchyFine Q M G P J) (1/dn)
    radialIndex (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
    (publicRadialCurvature n ρ) (publicRadialRadius n R) dn

theorem physicalHierarchyExtension_contDiff {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J s : ℕ)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hw : ∀ i : Fin J,0<(G (i.val+1) []).width) :
    ContDiff ℝ 3 (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn) :=
  total_contDiff coarseIndex (physicalHierarchyCoarse Q M G P J) _
    (outerPhysicalCoarseFamily_contDiff J Q M (baseMacroProjection J n D) G
      (baseOrdinaryProjection J n D) (basePhysicalProjection J n D) P J)
    (fun i => ChiOuter.coarseWidth_pos G _ (hw i)) fineIndex _ _ radialIndex _ _ _ _ dn

theorem physicalHierarchyExtension_zero_trace {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J s : ℕ)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hw : ∀ i : Fin J,0<(G (i.val+1) []).width)
    (x : PhysicalBase E J n D) :
    physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn (pack x 0)=0 :=
  total_zero_trace coarseIndex (physicalHierarchyCoarse Q M G P J) _
    (fun i => ChiOuter.coarseWidth_pos G _ (hw i)) fineIndex _ _ radialIndex _ _ _ _ dn x

theorem physicalHierarchyExtension_normal_readout {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J s : ℕ)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hdn : dn≠0) (hw : ∀ i : Fin J,0<(G (i.val+1) []).width)
    (hR : ∀ i : Fin J,0<R (i.val+1)) (x : PhysicalBase E J n D) :
    dn*normalReadout s (gradient (fun q : Normals s =>
      physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn (pack x q)) 0)=
      (∑ i : Fin J,physicalHierarchyCoarse Q M G P J i x)+(physicalHierarchyFine Q M G P J).r x+
        ∑ i : Fin J,RadialWrapper.bowl (publicRadialCurvature n ρ i) (publicRadialRadius n R i)
          (publicRadialProjection n D i x) :=
  total_normal_readout coarseIndex (physicalHierarchyCoarse Q M G P J) _
    (fun i => ChiOuter.coarseWidth_pos G _ (hw i)) fineIndex _ radialIndex _ _ _ _ dn hdn
    (publicRadialRadius_pos n R hR) x

theorem physicalHierarchyExtension_carrier_trace {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (j s : ℕ)
    (coarseIndex radialIndex : Fin (j+1) → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hdn : dn≠0) (hw : ∀ i : Fin (j+1),0<(G (i.val+1) []).width)
    (hR : ∀ i : Fin (j+1),0<R (i.val+1)) (x : PhysicalBase E (j+1) n D) :
    outerPhysicalCarrier (j+1) Q M (baseMacroProjection (j+1) n D) G
      (baseOrdinaryProjection (j+1) n D) (basePhysicalProjection (j+1) n D) (j+1) 0 x+
      RadialWrapper.bowl (ρ 0) (R 0) (block (j+1) 0 x.snd.fst)+
      dn*normalReadout s (gradient (fun q : Normals s =>
        physicalHierarchyExtension Q M G P (j+1) s coarseIndex radialIndex fineIndex ρ R dn (pack x q)) 0)=
      (∑ i : Fin (j+2),outerPhysicalCarrier (j+1) Q M (baseMacroProjection (j+1) n D) G
        (baseOrdinaryProjection (j+1) n D) (basePhysicalProjection (j+1) n D) (j+1) i.val x)+
        physicalPublic ρ R (j+1) 0 (padded x.snd.fst) x.snd.snd := by
  rw [physicalHierarchyExtension_normal_readout Q M G P (j+1) s coarseIndex radialIndex fineIndex ρ R dn hdn hw hR x]
  change _+_+((∑ i : Fin (j+1),outerPhysicalCoarseFamily (j+1) Q M (baseMacroProjection (j+1) n D) G
      (baseOrdinaryProjection (j+1) n D) (basePhysicalProjection (j+1) n D) P (j+1) i x)+
      outerPhysicalFineFrontier (j+1) Q M (baseMacroProjection (j+1) n D) G
        (baseOrdinaryProjection (j+1) n D) (basePhysicalProjection (j+1) n D) P (j+1) x+_)=_
  rw [outer_physical_coarse_fine_trace]
  rw [Fin.sum_univ_succ (fun i : Fin (j+2) => outerPhysicalCarrier (j+1) Q M (baseMacroProjection (j+1) n D) G
    (baseOrdinaryProjection (j+1) n D) (basePhysicalProjection (j+1) n D) (j+1) i.val x)]
  rw [← physical_public_channel_sum ρ R j x]
  simp only [Fin.val_zero,Fin.val_succ]
  ring

end Bilevel.EndpointTransportResponse
