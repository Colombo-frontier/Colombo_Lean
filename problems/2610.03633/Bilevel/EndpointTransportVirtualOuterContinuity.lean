import Bilevel.EndpointTransportVirtualContinuity
import Bilevel.ChiVirtualOuterContinuity
import Bilevel.ChiVirtualFormulaContinuity

/-! Joint continuity of the entire disclosed-data physical lower scalar,
including macro selection, every normal term, and the public radial sum.
The result holds on all arrays, before imposing valid-prefix conditions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev PhysicalPrefixData {D : ℕ} (M : Node E) (G : Geometry (Block D)) (n : ℕ) :=
  (Fin (M.n+1) → E) × PhysicalColumnData G n

theorem physicalMacroData_continuous {J n D : ℕ} (M : Node E) (G : Geometry (Block D)) :
    Continuous (fun p : PhysicalPrefixData M G n × PhysicalBase E J n D => (p.1.1,p.2.fst)) :=
  continuous_fst.fst.prodMk ((jointFstLinear (A:=E)
    (B:=HybridTangent (Blocks J (Block D)) n D)).continuous.comp continuous_snd)

theorem physicalInnerData_continuous {J n D : ℕ} (M : Node E) (G : Geometry (Block D)) :
    Continuous (fun p : PhysicalPrefixData M G n × PhysicalBase E J n D => (p.1.2,p.2.snd)) :=
  continuous_fst.snd.prodMk ((jointSndLinear (A:=E)
    (B:=HybridTangent (Blocks J (Block D)) n D)).continuous.comp continuous_snd)

theorem prefixPhysicalOuterCoarse_continuous {J n D : ℕ} (M : Node E) (G : Geometry (Block D))
    (P : ChiFine.Parameters) (rM : ℕ) (r rs : ℕ → List ℕ → ℕ) (i : Fin J) :
    Continuous (fun p : PhysicalPrefixData M G n × PhysicalBase E J n D =>
      prefixPhysicalOuterCoarse M G P rM r rs p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 i p.2) := by
  unfold prefixPhysicalOuterCoarse
  apply continuous_finset_sum
  intro l _
  exact ((virtualOuterSelector_continuous M rM l).comp (physicalMacroData_continuous M G)).mul
    ((virtualPhysicalCoarseCarrier_continuous G P r rs J 0 [l.val] (i.val+1)).comp
      (physicalInnerData_continuous M G))

theorem prefixPhysicalOuterFinePiece_continuous {J n D : ℕ} (M : Node E) (G : Geometry (Block D))
    (P : ChiFine.Parameters) (rM : ℕ) (r rs : ℕ → List ℕ → ℕ) (k : ℕ) :
    Continuous (fun p : PhysicalPrefixData M G n × PhysicalBase E J n D =>
      prefixPhysicalOuterFinePiece M G P rM r rs p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 k p.2) := by
  unfold prefixPhysicalOuterFinePiece
  apply continuous_finset_sum
  intro l _
  exact ((virtualOuterSelector_continuous M rM l).comp (physicalMacroData_continuous M G)).mul
    ((virtualPhysicalFinePiece_continuous G P r rs k J 0 [l.val]).comp
      (physicalInnerData_continuous M G))

theorem physicalFullData_continuous {J n D s : ℕ} (M : Node E) (G : Geometry (Block D)) :
    Continuous (fun p : PhysicalPrefixData M G n × Full (PhysicalBase E J n D) s => (p.1,p.2.fst)) :=
  continuous_fst.prodMk ((jointFstLinear (A:=PhysicalBase E J n D) (B:=Normals s)).continuous.comp continuous_snd)

theorem physicalFullNormal_continuous {J n D s : ℕ} (M : Node E) (G : Geometry (Block D)) (i : Fin s) :
    Continuous (fun p : PhysicalPrefixData M G n × Full (PhysicalBase E J n D) s => p.2.snd i) :=
  (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp
    ((jointSndLinear (A:=PhysicalBase E J n D) (B:=Normals s)).continuous.comp continuous_snd)

theorem prefixPhysicalHierarchyExtension_continuous {J n D s : ℕ}
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ) (r rs : ℕ → List ℕ → ℕ) :
    Continuous (fun p : PhysicalPrefixData M G n × Full (PhysicalBase E J n D) s =>
      prefixPhysicalHierarchyExtension M G P index radialIndex fineIndex ρ R dn rM r rs
        p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  unfold prefixPhysicalHierarchyExtension
  apply Continuous.add
  · apply continuous_const.mul
    apply Continuous.add
    · apply continuous_finset_sum
      intro i _
      exact ((prefixPhysicalOuterCoarse_continuous M G P rM r rs i).comp
        (physicalFullData_continuous M G)).mul
          ((normal_continuous_all _).comp (physicalFullNormal_continuous M G (index i)))
    · apply continuous_finset_sum
      intro k _
      exact ((prefixPhysicalOuterFinePiece_continuous M G P rM r rs k).comp
        (physicalFullData_continuous M G)).mul
          ((normal_continuous_all _).comp (physicalFullNormal_continuous M G fineIndex))
  · have hr := (radialSum_contDiff radialIndex (publicRadialProjection (E:=E) (J:=J) n D)
      (publicRadialProjection_norm_le (E:=E) (J:=J) n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) dn).continuous
    have hc := hr.comp (continuous_snd : Continuous
      (Prod.snd : PhysicalPrefixData M G n × Full (PhysicalBase E J n D) s → _))
    exact hc

abbrev PhysicalPrefixState {D : ℕ} (M : Node E) (G : Geometry (Block D)) (n : ℕ) :=
  ℕ × PhysicalPrefixData M G n

def statePhysicalPotential {J n D s : ℕ} (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) (p : PhysicalPrefixState M G n) :
    Full (PhysicalBase E J n D) s → ℝ :=
  prefixPhysicalHierarchyExtension M G P index radialIndex fineIndex ρ R dn (rM p.1) (r p.1) (rs p.1)
    p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

theorem statePhysicalPotential_continuous {J n D s : ℕ}
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ → ℕ) (r rs : ℕ → ℕ → List ℕ → ℕ) :
    Continuous (Function.uncurry (statePhysicalPotential (n:=n) M G P index radialIndex fineIndex ρ R dn rM r rs)) := by
  have h : Continuous (fun p : ℕ × (PhysicalPrefixData M G n × Full (PhysicalBase E J n D) s) =>
      prefixPhysicalHierarchyExtension M G P index radialIndex fineIndex ρ R dn (rM p.1) (r p.1) (rs p.1)
        p.2.1.1 p.2.1.2.1 p.2.1.2.2.1 p.2.1.2.2.2 p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun q =>
      prefixPhysicalHierarchyExtension_continuous M G P index radialIndex fineIndex ρ R dn (rM q) (r q) (rs q))
  have hc := h.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  exact hc

end Bilevel.EndpointTransportResponse
