import Bilevel.EndpointTransportVirtualFullRestriction
import Bilevel.EndpointTransportCompletionRadialRestriction

/-! The explicit physical prefix scalar is the restriction of one actual
completed hierarchy along a linear isometry. Thus the full global jets,
including mixed normal/tangent derivatives, inherit their original bounds. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1400000
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {J n D D' s : ℕ}
    (M : Node E) (VM : Space M.n →ₗᵢ[ℝ] F)
    (G : Geometry (Block D)) (V : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D')
    (Q : Rotations n D') (P : ChiFine.Parameters)
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (MI : E →ₗᵢ[ℝ] F) (BI : Block D →ₗᵢ[ℝ] Block D')
    (hm : ∀ a,(nodeWithFrame M VM).coordinates (MI a)=readout M.n rM M.radius macroColumns a)
    (hc : ∀ j I,j<J → ∀ u,(geometryWithFrames G V j I).coordinates (BI u)=
      readout (G j I).n (r j I) (G j I).radius (columns j I) u)
    (hp : ∀ I u,physicalCoordinates Q (geometryWithFrames G V J I) (physicalMap BI u)=
      prefixPhysicalCoordinatesAt (G J I) (sourceCount J I) (r J I) (sourceColumns J I) (targetColumns J I) u)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)

include hm hc hp in
theorem completed_physicalHierarchyExtension_restriction :
    physicalHierarchyExtension Q (nodeWithFrame M VM) (geometryWithFrames G V) P J s
      coarseIndex radialIndex fineIndex ρ R dn ∘ completionFullMap s MI BI=
    prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn rM r sourceCount
      macroColumns columns sourceColumns targetColumns := by
  funext z
  apply rebuilt_physicalHierarchyExtension_eq_virtual M VM G V Q P rM r sourceCount
    macroColumns columns sourceColumns targetColumns z.fst.fst (MI z.fst.fst) z.fst.snd
      (completionTangentMap BI z.fst.snd) (hm z.fst.fst) ?_ (fun I => hp I z.fst.snd.snd)
      coarseIndex radialIndex fineIndex ρ R dn z.snd ?_
  · intro j I hj
    change (geometryWithFrames G V j I).coordinates (block J j (blocksMap J BI z.fst.snd.fst))=_
    rw [block_blocksMap]
    exact hc j I hj _
  · exact publicRadialSum_completion MI BI radialIndex ρ R dn z

include hm hc hp in
theorem prefix_physicalHierarchyExtension_jets
    (hf : ContDiff ℝ 3 (physicalHierarchyExtension Q (nodeWithFrame M VM) (geometryWithFrames G V) P J s
      coarseIndex radialIndex fineIndex ρ R dn))
    (k : ℕ) (hk : k≤3) (C : ℝ)
    (hb : ∀ z,‖iteratedFDeriv ℝ k (physicalHierarchyExtension Q (nodeWithFrame M VM)
      (geometryWithFrames G V) P J s coarseIndex radialIndex fineIndex ρ R dn) z‖≤C) :
    ContDiff ℝ 3 (prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
      rM r sourceCount macroColumns columns sourceColumns targetColumns) ∧
    ∀ z,‖iteratedFDeriv ℝ k (prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn
      rM r sourceCount macroColumns columns sourceColumns targetColumns) z‖≤C := by
  have he := completed_physicalHierarchyExtension_restriction M VM G V Q P rM r sourceCount
    macroColumns columns sourceColumns targetColumns MI BI hm hc hp coarseIndex radialIndex fineIndex ρ R dn
  rw [← he]
  refine ⟨hf.comp (completionFullMap s MI BI).toContinuousLinearMap.contDiff,?_⟩
  intro z
  exact (isometric_jet_restriction (completionFullMap s MI BI) _ hf z k hk).trans (hb _)

end Bilevel.EndpointTransportResponse
