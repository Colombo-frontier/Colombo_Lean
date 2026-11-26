import Bilevel.EndpointTransportSliceIdentity
import Bilevel.EndpointTransportPayloadPrefix
import Bilevel.ChiVirtualOuter

/-! Literal disclosed-data formula for the J-layer physical lower extension.
Source and target counts are independent: the source store may advance once,
while the target store remains the prebatch store. No hidden frame or rotation
is evaluated. Future leaves therefore need no prospective source column. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiExtension ZeroChainSchedule

def prefixPhysicalCoordinatesAt {n D : ℕ} (N : Node (Block D)) (rs rt : ℕ)
    (sourceColumns targetColumns : Fin (N.n+1) → Physical n D) (Y : Physical n D) : ChiSplitChain.Latent N.n :=
  pack ((2:ℝ) • ChiPrefixEvaluation.readout N.n rs (gamma n*N.radius) sourceColumns Y)
    (ChiPrefixEvaluation.readout N.n rt (gamma n*N.radius) targetColumns Y)

theorem prefixPhysicalCoordinatesAt_succ {n D : ℕ} (N : Node (Block D)) (r : ℕ)
    (sourceColumns targetColumns : Fin (N.n+1) → Physical n D) :
    prefixPhysicalCoordinatesAt N (r+1) r sourceColumns targetColumns=
      physicalPrefixCoordinates N r sourceColumns targetColumns := rfl

def prefixPhysicalRelease {n D : ℕ} (N : Node (Block D)) (rt : ℕ)
    (targetColumns : Fin (N.n+1) → Physical n D) (Y : Physical n D) : ℝ :=
  releaseGate (ChiPrefixEvaluation.readout N.n rt (gamma n*N.radius) targetColumns Y (Fin.last N.n)/N.parentWidth)

def prefixPhysicalPayloadAt {n D : ℕ} (N : Node (Block D)) (rs rt : ℕ)
    (sourceColumns targetColumns : Fin (N.n+1) → Physical n D) (Y : Physical n D) : ℝ :=
  ChiSplitChain.payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius
    (prefixPhysicalCoordinatesAt N rs rt sourceColumns targetColumns Y)

def physicalNodeOrigin {D : ℕ} (N : Node (Block D)) : ℝ :=
  payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius 0

def virtualPhysicalCarrier {m n D : ℕ} (G : Geometry (Block D))
    (r sourceCount : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D) :
    ℕ → ℕ → List ℕ → ℕ → HybridTangent (Blocks m (Block D)) n D → ℝ
  | 0,j,I,0,x => prefixPhysicalPayloadAt (G j I) (sourceCount j I) (r j I)
      (sourceColumns j I) (targetColumns j I) x.snd-physicalNodeOrigin (G j I)
  | 0,_,_,_+1,_ => 0
  | d+1,j,I,0,x => if d=0 then
      virtualH (G j I) (r j I) (columns j I) (block m j x.fst)+
        ∑ i : Fin ((G j I).n+1),virtualResidual (G j I) (r j I) (columns j I) i (block m j x.fst)*
          (prefixPhysicalRelease (G (j+1) (child I i.val)) (r (j+1) (child I i.val))
            (targetColumns (j+1) (child I i.val)) x.snd-1)
      else virtualCarrier G r columns (d+1) j I 0 (padded x.fst)
  | d+1,j,I,t+1,x => ∑ i : Fin ((G j I).n+1),
      virtualSelector (G j I) (r j I) (columns j I) i (block m j x.fst)*
        virtualPhysicalCarrier G r sourceCount columns sourceColumns targetColumns d (j+1) (child I i.val) t x

def virtualPhysicalSelect {m n D : ℕ} (G : Geometry (Block D)) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (leaf : ℕ → List ℕ → Physical n D → ℝ) :
    ℕ → ℕ → List ℕ → HybridTangent (Blocks m (Block D)) n D → ℝ
  | 0,j,I,x => leaf j I x.snd
  | d+1,j,I,x => ∑ i : Fin ((G j I).n+1),
      virtualSelector (G j I) (r j I) (columns j I) i (block m j x.fst)*
        virtualPhysicalSelect G r columns leaf d (j+1) (child I i.val) x

def virtualPhysicalFrontier {m n D : ℕ} (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (r sourceCount : ℕ → List ℕ → ℕ) (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (d j : ℕ) (I : List ℕ) : HybridTangent (Blocks m (Block D)) n D → ℝ :=
  virtualPhysicalSelect G r columns (fun k A Y => ChiSplitFine.frontier (G k A).n P.ℓ P.β
    (prefixPhysicalCoordinatesAt (G k A) (sourceCount k A) (r k A) (sourceColumns k A) (targetColumns k A) Y)) d j I

def virtualPhysicalFinePiece {m n D : ℕ} (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (r sourceCount : ℕ → List ℕ → ℕ) (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (p d j : ℕ) (I : List ℕ) : HybridTangent (Blocks m (Block D)) n D → ℝ :=
  virtualPhysicalSelect G r columns (fun k A Y => ChiSplitFine.pieces P (G k A).n p
    (prefixPhysicalCoordinatesAt (G k A) (sourceCount k A) (r k A) (sourceColumns k A) (targetColumns k A) Y)) d j I

def virtualPhysicalCoarseCarrier {m n D : ℕ} (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (r sourceCount : ℕ → List ℕ → ℕ) (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (d j : ℕ) (I : List ℕ) (t : ℕ) (x : HybridTangent (Blocks m (Block D)) n D) : ℝ :=
  virtualPhysicalCarrier G r sourceCount columns sourceColumns targetColumns d j I t x-
    if t=d then virtualPhysicalFrontier G P r sourceCount columns sourceColumns targetColumns d j I x else 0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def prefixPhysicalOuterCoarse {J n D : ℕ} (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (i : Fin J) (x : PhysicalBase E J n D) : ℝ :=
  ∑ l : Fin (M.n+1),virtualOuterSelector M rM macroColumns l x.fst*
    virtualPhysicalCoarseCarrier G P r sourceCount columns sourceColumns targetColumns J 0 [l.val] (i.val+1) x.snd

def prefixPhysicalOuterFinePiece {J n D : ℕ} (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (p : ℕ) (x : PhysicalBase E J n D) : ℝ :=
  ∑ l : Fin (M.n+1),virtualOuterSelector M rM macroColumns l x.fst*
    virtualPhysicalFinePiece G P r sourceCount columns sourceColumns targetColumns p J 0 [l.val] x.snd

def prefixPhysicalHierarchyExtension {J n D s : ℕ} (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (z : Full (PhysicalBase E J n D) s) : ℝ :=
  (1/dn)*((∑ i : Fin J,prefixPhysicalOuterCoarse M G P rM r sourceCount macroColumns columns
    sourceColumns targetColumns i z.fst*SmallGapProfiles.normal (coarseWidth G (i.val+1)) (z.snd (coarseIndex i)))+
    ∑ p ∈ Finset.range (levels P.θ+1),prefixPhysicalOuterFinePiece M G P rM r sourceCount macroColumns columns
      sourceColumns targetColumns p z.fst*SmallGapProfiles.normal (width P.c P.β P.θ p) (z.snd fineIndex))+
    radialSum radialIndex (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) dn z

end Bilevel.EndpointTransportResponse
