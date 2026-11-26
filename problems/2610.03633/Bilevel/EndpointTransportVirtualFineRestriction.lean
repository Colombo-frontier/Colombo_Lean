import Bilevel.EndpointTransportVirtualRestriction

/-! Restriction of actual selected fine leaves and coarse carriers through
all ordinary ancestors. Terminal source/target counts may differ. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {m n D D' : ℕ}

theorem rebuilt_physicalSelect_eq_virtual
    (G : Geometry (Block D)) (V : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D')
    (J : ℕ) (r : ℕ → List ℕ → ℕ) (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (leaf : ℕ → List ℕ → HybridTangent (Blocks m (Block D')) n D' → ℝ)
    (virtualLeaf : ℕ → List ℕ → Physical n D → ℝ)
    (x : HybridTangent (Blocks m (Block D)) n D) (y : HybridTangent (Blocks m (Block D')) n D')
    (hc : ∀ j I,j<J → (geometryWithFrames G V j I).coordinates (block m j y.fst)=
      readout (G j I).n (r j I) (G j I).radius (columns j I) (block m j x.fst))
    (hl : ∀ I,leaf J I y=virtualLeaf J I x.snd)
    (d j : ℕ) (I : List ℕ) (hd : j+d=J) :
    ChiLiftedCarrier.selectFamily m (geometryWithFrames G V)
      (jointFstLinear (A:=Blocks m (Block D')) (B:=Physical n D')) leaf d j I y=
      virtualPhysicalSelect G r columns virtualLeaf d j I x := by
  induction d generalizing j I with
  | zero =>
    have hj : j=J := by omega
    subst j
    exact hl I
  | succ d ih =>
    have hj : j<J := by omega
    change (∑ i : Fin ((G j I).n+1),(geometryWithFrames G V j I).selector i (block m j y.fst)*
      ChiLiftedCarrier.selectFamily m (geometryWithFrames G V) _ leaf d (j+1) (child I i.val) y)=_
    change _=∑ i : Fin ((G j I).n+1),virtualSelector (G j I) (r j I) (columns j I) i (block m j x.fst)*
      virtualPhysicalSelect G r columns virtualLeaf d (j+1) (child I i.val) x
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg₂ (fun a b : ℝ => a*b)
      (nodeWithFrame_selector_of_coordinates (G j I) (V j I) (r j I) (columns j I)
        (block m j x.fst) (block m j y.fst) (hc j I hj) i)
      (ih (j+1) (child I i.val) (by omega))

variable (G : Geometry (Block D)) (V : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D') (Q : Rotations n D')
    (P : ChiFine.Parameters) (J : ℕ) (r sourceCount : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (x : HybridTangent (Blocks m (Block D)) n D) (y : HybridTangent (Blocks m (Block D')) n D')
    (hc : ∀ j I,j<J → (geometryWithFrames G V j I).coordinates (block m j y.fst)=
      readout (G j I).n (r j I) (G j I).radius (columns j I) (block m j x.fst))
    (hp : ∀ I,physicalCoordinates Q (geometryWithFrames G V J I) y.snd=
      prefixPhysicalCoordinatesAt (G J I) (sourceCount J I) (r J I) (sourceColumns J I) (targetColumns J I) x.snd)

include hc hp in
theorem rebuilt_physicalFrontier_eq_virtual (d j : ℕ) (I : List ℕ) (hd : j+d=J) :
    selectedPhysicalFineFrontier m (geometryWithFrames G V)
      (jointFstLinear (A:=Blocks m (Block D')) (B:=Physical n D'))
      (jointSndLinear (A:=Blocks m (Block D')) (B:=Physical n D')) Q P d j I y=
      virtualPhysicalFrontier G P r sourceCount columns sourceColumns targetColumns d j I x := by
  apply rebuilt_physicalSelect_eq_virtual G V J r columns _ _ x y hc _ d j I hd
  intro I
  change ChiSplitFine.frontier (G J I).n P.ℓ P.β (physicalCoordinates Q (geometryWithFrames G V J I) y.snd)=_
  rw [hp I]

include hc hp in
theorem rebuilt_physicalFinePiece_eq_virtual (p d j : ℕ) (I : List ℕ) (hd : j+d=J) :
    selectedPhysicalFinePiece m (geometryWithFrames G V)
      (jointFstLinear (A:=Blocks m (Block D')) (B:=Physical n D'))
      (jointSndLinear (A:=Blocks m (Block D')) (B:=Physical n D')) Q P p d j I y=
      virtualPhysicalFinePiece G P r sourceCount columns sourceColumns targetColumns p d j I x := by
  apply rebuilt_physicalSelect_eq_virtual G V J r columns _ _ x y hc _ d j I hd
  intro I
  change ChiSplitFine.pieces P (G J I).n p (physicalCoordinates Q (geometryWithFrames G V J I) y.snd)=_
  rw [hp I]

include hc hp in
theorem rebuilt_physicalCoarseCarrier_eq_virtual (d j : ℕ) (I : List ℕ) (t : ℕ) (hd : j+d=J) :
    physicalCoarseCarrier m Q (geometryWithFrames G V)
      (jointFstLinear (A:=Blocks m (Block D')) (B:=Physical n D'))
      (jointSndLinear (A:=Blocks m (Block D')) (B:=Physical n D')) P d j I t y=
      virtualPhysicalCoarseCarrier G P r sourceCount columns sourceColumns targetColumns d j I t x := by
  unfold physicalCoarseCarrier virtualPhysicalCoarseCarrier
  rw [rebuilt_physicalCarrier_eq_virtual G V Q J r sourceCount columns sourceColumns targetColumns x y hc hp d j I t hd]
  split_ifs
  · rw [rebuilt_physicalFrontier_eq_virtual G V Q P J r sourceCount columns sourceColumns targetColumns x y hc hp d j I hd]
  · rfl

end Bilevel.EndpointTransportResponse
