import Bilevel.EndpointTransportVirtualFormula
import Bilevel.ChiVirtualFrameIrrelevance

/-! Every physical prefix scalar ignores the unused source-frame fields.
It can therefore use a fixed public numeric template on all disclosed data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension

@[simp] theorem prefixPhysicalCoordinatesAt_reframe {n D : ℕ} (N : Node (Block D))
    (U : Space N.n →ₗᵢ[ℝ] Block D) (rs rt : ℕ)
    (S T : Fin (N.n+1) → Physical n D) (Y : Physical n D) :
    prefixPhysicalCoordinatesAt (reframeNode N U) rs rt S T Y=prefixPhysicalCoordinatesAt N rs rt S T Y := rfl

@[simp] theorem prefixPhysicalRelease_reframe {n D : ℕ} (N : Node (Block D))
    (U : Space N.n →ₗᵢ[ℝ] Block D) (rt : ℕ)
    (T : Fin (N.n+1) → Physical n D) (Y : Physical n D) :
    prefixPhysicalRelease (reframeNode N U) rt T Y=prefixPhysicalRelease N rt T Y := rfl

variable {m n D : ℕ} (G : Geometry (Block D))
  (U : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D)
  (r rs : ℕ → List ℕ → ℕ) (C : ∀ j I,Fin ((G j I).n+1) → Block D)
  (S T : ∀ j I,Fin ((G j I).n+1) → Physical n D)

@[simp] theorem virtualPhysicalCarrier_reframe (d j : ℕ) (I : List ℕ) (k : ℕ)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalCarrier (reframeGeometry G U) r rs C S T d j I k x=
      virtualPhysicalCarrier G r rs C S T d j I k x := by
  induction d generalizing j I k with
  | zero => cases k <;> rfl
  | succ d ih =>
    cases k with
    | zero =>
      simp only [virtualPhysicalCarrier,virtualCarrier_reframe]
      split_ifs
      · simp only [reframeGeometry,virtualH_reframe,virtualResidual_reframe,prefixPhysicalRelease_reframe]
        rfl
      · rfl
    | succ k =>
      simp only [virtualPhysicalCarrier,reframeGeometry,virtualSelector_reframe,ih]
      rfl

@[simp] theorem virtualPhysicalSelect_reframe
    (leaf : ℕ → List ℕ → Physical n D → ℝ) (d j : ℕ) (I : List ℕ)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalSelect (reframeGeometry G U) r C leaf d j I x=virtualPhysicalSelect G r C leaf d j I x := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    simp only [virtualPhysicalSelect,reframeGeometry,virtualSelector_reframe,ih]
    rfl

@[simp] theorem virtualPhysicalFrontier_reframe (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalFrontier (reframeGeometry G U) P r rs C S T d j I x=
      virtualPhysicalFrontier G P r rs C S T d j I x := by
  unfold virtualPhysicalFrontier
  simpa only [reframeGeometry,prefixPhysicalCoordinatesAt_reframe] using
    virtualPhysicalSelect_reframe G U r C
      (fun k A Y => ChiSplitFine.frontier (G k A).n P.ℓ P.β
        (prefixPhysicalCoordinatesAt (G k A) (rs k A) (r k A) (S k A) (T k A) Y)) d j I x

@[simp] theorem virtualPhysicalFinePiece_reframe (P : ChiFine.Parameters) (p d j : ℕ) (I : List ℕ)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalFinePiece (reframeGeometry G U) P r rs C S T p d j I x=
      virtualPhysicalFinePiece G P r rs C S T p d j I x := by
  unfold virtualPhysicalFinePiece
  simpa only [reframeGeometry,prefixPhysicalCoordinatesAt_reframe] using
    virtualPhysicalSelect_reframe G U r C
      (fun k A Y => ChiSplitFine.pieces P (G k A).n p
        (prefixPhysicalCoordinatesAt (G k A) (rs k A) (r k A) (S k A) (T k A) Y)) d j I x

@[simp] theorem virtualPhysicalCoarseCarrier_reframe (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (t : ℕ)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalCoarseCarrier (reframeGeometry G U) P r rs C S T d j I t x=
      virtualPhysicalCoarseCarrier G P r rs C S T d j I t x := by
  simp only [virtualPhysicalCoarseCarrier,virtualPhysicalCarrier_reframe,virtualPhysicalFrontier_reframe]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E) (rM : ℕ) (CM : Fin (M.n+1) → E)

@[simp] theorem prefixPhysicalOuterCoarse_reframe {J : ℕ} (P : ChiFine.Parameters)
    (i : Fin J) (x : PhysicalBase E J n D) :
    prefixPhysicalOuterCoarse (reframeNode M UM) (reframeGeometry G U) P rM r rs CM C S T i x=
      prefixPhysicalOuterCoarse M G P rM r rs CM C S T i x := by
  simp only [prefixPhysicalOuterCoarse,virtualOuterSelector_reframe,virtualPhysicalCoarseCarrier_reframe]
  rfl

@[simp] theorem prefixPhysicalOuterFinePiece_reframe {J : ℕ} (P : ChiFine.Parameters)
    (k : ℕ) (x : PhysicalBase E J n D) :
    prefixPhysicalOuterFinePiece (reframeNode M UM) (reframeGeometry G U) P rM r rs CM C S T k x=
      prefixPhysicalOuterFinePiece M G P rM r rs CM C S T k x := by
  simp only [prefixPhysicalOuterFinePiece,virtualOuterSelector_reframe,virtualPhysicalFinePiece_reframe]
  rfl

@[simp] theorem prefixPhysicalHierarchyExtension_reframe {J s : ℕ} (P : ChiFine.Parameters)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (x : Full (PhysicalBase E J n D) s) :
    prefixPhysicalHierarchyExtension (reframeNode M UM) (reframeGeometry G U) P index radialIndex fineIndex ρ R dn
      rM r rs CM C S T x=
      prefixPhysicalHierarchyExtension M G P index radialIndex fineIndex ρ R dn rM r rs CM C S T x := by
  have hw : ChiOuter.coarseWidth (reframeGeometry G U)=ChiOuter.coarseWidth G := rfl
  simp only [prefixPhysicalHierarchyExtension,hw,prefixPhysicalOuterCoarse_reframe,prefixPhysicalOuterFinePiece_reframe]

end Bilevel.EndpointTransportResponse
