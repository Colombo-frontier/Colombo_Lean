import Bilevel.ChiVirtualFormula
import Bilevel.ChiVirtualOuterContinuity

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension ZeroChainSchedule
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem normal_continuous_all (W : ℝ) : Continuous (SmallGapProfiles.normal W) := by
  exact (SmallGapProfiles.normal_contDiff_all W (k := 0)).continuous

omit [CompleteSpace E] [CompleteSpace F] in
theorem fullData_continuous (m s : ℕ) (M : Node E) (D : Geometry F) :
    Continuous (fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s => (p.1,p.2.fst)) :=
  continuous_fst.prodMk
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Joint E (Blocks m F)) (Normals s)).continuous.fst.comp continuous_snd)

omit [CompleteSpace E] [CompleteSpace F] in
theorem fullNormal_continuous (m s : ℕ) (M : Node E) (D : Geometry F) (i : Fin s) :
    Continuous (fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s => p.2.snd i) :=
  (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Joint E (Blocks m F)) (Normals s)).continuous.snd.comp continuous_snd)

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualCoarse_full_continuous (m s : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (J : ℕ) (i : Fin J) :
    Continuous (fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s =>
      virtualCoarse m M D rM r p.1.1 p.1.2 J i p.2.fst) := by
  exact Continuous.comp
    (f := fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s => (p.1,p.2.fst))
    (g := fun p : HierarchyData M D × Joint E (Blocks m F) => virtualCoarse m M D rM r p.1.1 p.1.2 J i p.2)
    (virtualCoarse_continuous m M D rM r J i) (fullData_continuous m s M D)

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualLeaf_full_continuous (m s : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (leaf : ∀ j I,Space (D j I).n → ℝ)
    (hl : ∀ j I,Continuous (leaf j I)) (J : ℕ) :
    Continuous (fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s =>
      virtualOuterLeaf m M D rM r p.1.1 p.1.2 leaf J p.2.fst) := by
  exact Continuous.comp
    (f := fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s => (p.1,p.2.fst))
    (g := fun p : HierarchyData M D × Joint E (Blocks m F) => virtualOuterLeaf m M D rM r p.1.1 p.1.2 leaf J p.2)
    (virtualOuterLeaf_continuous m M D rM r leaf hl J) (fullData_continuous m s M D)

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualActive_continuous (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (c θ : ℝ) (s : ℕ) (index radialIndex : Fin J → Fin s)
    (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ) :
    Continuous (fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s =>
      virtualActive m M D J rM r p.1.1 p.1.2 c θ s index radialIndex fineIndex rad R dn p.2) := by
  unfold virtualActive
  apply Continuous.add
  · apply continuous_const.mul
    apply Continuous.add
    · apply continuous_finset_sum
      intro i _
      exact (virtualCoarse_full_continuous m s M D rM r J i).mul
        ((normal_continuous_all _).comp (fullNormal_continuous m s M D (index i)))
    · apply continuous_finset_sum
      intro p _
      apply (virtualLeaf_full_continuous m s M D rM r (pieceLeaf D c θ p) (fun j I =>
        (ZeroChainResidualScaled.scaled_contDiff
          (ChiFine.piece_contDiff (D j I).n (levels θ) (resolution c 1 θ) p)
          ((D j I).ell*(D j I).width^2) (D j I).width).continuous) J).mul
      exact (normal_continuous_all _).comp (fullNormal_continuous m s M D fineIndex)
  · exact (radialSum_contDiff radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
      (fun i => hierarchyBlock_norm_le m (i.val+1)) (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn).continuous.comp continuous_snd

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualSignal_continuous (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (c θ : ℝ) (s : ℕ) (fineIndex : Fin s) :
    Continuous (fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s =>
      virtualSignal m M D J rM r p.1.1 p.1.2 c θ s fineIndex p.2) := by
  unfold virtualSignal
  apply (virtualLeaf_full_continuous m s M D rM r
    (signalLeaf D (width c (D J []).width θ (levels θ)/8)) (fun j I =>
      (ChiFine.signalResidual_contDiff (D j I).n (D j I).ell (D j I).width _).continuous) J).mul
  exact (normal_continuous_all _).comp (fullNormal_continuous m s M D fineIndex)

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualInactive_continuous (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (c θ : ℝ) (s : ℕ) (index radialIndex : Fin J → Fin s)
    (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ) :
    Continuous (fun p : HierarchyData M D × Full (Joint E (Blocks m F)) s =>
      virtualInactive m M D J rM r p.1.1 p.1.2 c θ s index radialIndex fineIndex rad R dn p.2) :=
  (virtualActive_continuous m M D J rM r c θ s index radialIndex fineIndex rad R dn).sub
    ((virtualSignal_continuous m M D J rM r c θ s fineIndex).div_const dn)

end Bilevel.ChiPrefixEvaluation
