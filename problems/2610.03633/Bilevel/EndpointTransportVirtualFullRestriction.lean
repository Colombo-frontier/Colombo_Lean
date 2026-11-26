import Bilevel.EndpointTransportVirtualFineRestriction

/-! Exact cross-dimension restriction of the complete physical normal
extension. Public radial equality is explicit and supplied by the actual
isometric completion; hidden coarse/fine terms are derived recursively. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiPrefixEvaluation
  ChiOuter ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1400000
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem nodeWithFrame_outerSelector_of_coordinates (M : Node E) (VM : Space M.n →ₗᵢ[ℝ] F)
    (rM : ℕ) (columns : Fin (M.n+1) → E) (a : E) (b : F)
    (h : (nodeWithFrame M VM).coordinates b=readout M.n rM M.radius columns a) (i : Fin (M.n+1)) :
    wrappedSelector (nodeWithFrame M VM) i b=virtualOuterSelector M rM columns i a := by
  change ChiOuter.selector M.n i (M.width⁻¹ • (nodeWithFrame M VM).coordinates b)=_
  rw [h]
  rfl

variable {J n D D' : ℕ}
    (M : Node E) (VM : Space M.n →ₗᵢ[ℝ] F)
    (G : Geometry (Block D)) (V : ∀ j I,Space (G j I).n →ₗᵢ[ℝ] Block D')
    (Q : Rotations n D') (P : ChiFine.Parameters)
    (rM : ℕ) (r sourceCount : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((G j I).n+1) → Block D)
    (sourceColumns targetColumns : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (a : E) (b : F)
    (x : HybridTangent (Blocks J (Block D)) n D) (y : HybridTangent (Blocks J (Block D')) n D')
    (hm : (nodeWithFrame M VM).coordinates b=readout M.n rM M.radius macroColumns a)
    (hc : ∀ j I,j<J → (geometryWithFrames G V j I).coordinates (block J j y.fst)=
      readout (G j I).n (r j I) (G j I).radius (columns j I) (block J j x.fst))
    (hp : ∀ I,physicalCoordinates Q (geometryWithFrames G V J I) y.snd=
      prefixPhysicalCoordinatesAt (G J I) (sourceCount J I) (r J I) (sourceColumns J I) (targetColumns J I) x.snd)

include hm hc hp in
theorem rebuilt_physicalHierarchyCoarse_eq_virtual (i : Fin J) :
    physicalHierarchyCoarse Q (nodeWithFrame M VM) (geometryWithFrames G V) P J i (pack b y)=
      prefixPhysicalOuterCoarse M G P rM r sourceCount macroColumns columns sourceColumns targetColumns i (pack a x) := by
  rw [physicalHierarchyCoarse_slice]
  change _=∑ l : Fin (M.n+1),virtualOuterSelector M rM macroColumns l a*
    virtualPhysicalCoarseCarrier G P r sourceCount columns sourceColumns targetColumns J 0 [l.val] (i.val+1) x
  apply Finset.sum_congr rfl
  intro l _
  rw [nodeWithFrame_outerSelector_of_coordinates M VM rM macroColumns a b hm l]
  congr 1
  exact rebuilt_physicalCoarseCarrier_eq_virtual G V Q P J r sourceCount columns sourceColumns targetColumns x y hc hp J 0 [l.val] (i.val+1) (by omega)

include hm hc hp in
theorem rebuilt_physicalHierarchyFine_eq_virtual (p : ℕ) :
    (physicalHierarchyFine Q (nodeWithFrame M VM) (geometryWithFrames G V) P J).e p (pack b y)=
      prefixPhysicalOuterFinePiece M G P rM r sourceCount macroColumns columns sourceColumns targetColumns p (pack a x) := by
  rw [physicalHierarchyFine_piece_slice]
  change _=∑ l : Fin (M.n+1),virtualOuterSelector M rM macroColumns l a*
    virtualPhysicalFinePiece G P r sourceCount columns sourceColumns targetColumns p J 0 [l.val] x
  apply Finset.sum_congr rfl
  intro l _
  rw [nodeWithFrame_outerSelector_of_coordinates M VM rM macroColumns a b hm l]
  congr 1
  exact rebuilt_physicalFinePiece_eq_virtual G V Q P J r sourceCount columns sourceColumns targetColumns x y hc hp p J 0 [l.val] (by omega)

include hm hc hp in
theorem rebuilt_physicalHierarchyExtension_eq_virtual {s : ℕ}
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ) (q : Normals s)
    (hr : radialSum radialIndex (publicRadialProjection n D') (publicRadialProjection_norm_le n D')
      (publicRadialCurvature n ρ) (publicRadialRadius n R) dn (pack (pack b y) q)=
      radialSum radialIndex (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
        (publicRadialCurvature n ρ) (publicRadialRadius n R) dn (pack (pack a x) q)) :
    physicalHierarchyExtension Q (nodeWithFrame M VM) (geometryWithFrames G V) P J s coarseIndex radialIndex fineIndex ρ R dn
      (pack (pack b y) q)=
      prefixPhysicalHierarchyExtension M G P coarseIndex radialIndex fineIndex ρ R dn rM r sourceCount
        macroColumns columns sourceColumns targetColumns (pack (pack a x) q) := by
  unfold physicalHierarchyExtension total ChiExtension.hidden coarseSum
  rw [fineTerm_sum]
  simp only [normalTerm_formula]
  rw [hr]
  have hcoarse (i : Fin J) := rebuilt_physicalHierarchyCoarse_eq_virtual M VM G V Q P rM r sourceCount
    macroColumns columns sourceColumns targetColumns a b x y hm hc hp i
  have hfine (p : ℕ) := rebuilt_physicalHierarchyFine_eq_virtual M VM G V Q P rM r sourceCount
    macroColumns columns sourceColumns targetColumns a b x y hm hc hp p
  simp_rw [hcoarse,hfine]
  rfl

end Bilevel.EndpointTransportResponse
