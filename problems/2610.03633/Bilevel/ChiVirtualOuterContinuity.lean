import Bilevel.ChiVirtualFine
import Bilevel.ChiVirtualSelectionContinuity

/-! Joint continuity of the actual disclosed-data outer carrier and selected
leaf formulas, before imposing prefix Gram validity. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev HierarchyData (M : Node E) (D : Geometry F) := (Fin (M.n+1) → E) × ColumnData D

omit [CompleteSpace E] in
theorem virtualOuterSelector_continuous (M : Node E) (r : ℕ) (i : Fin (M.n+1)) :
    Continuous (fun p : (Fin (M.n+1) → E) × E => virtualOuterSelector M r p.1 i p.2) :=
  (ChiOuter.selector_contDiff M.n 3 i).continuous.comp
    ((readout_continuous M.n r M.radius).const_smul M.width⁻¹)

omit [CompleteSpace E] [CompleteSpace F] in
theorem macroData_continuous (m : ℕ) (M : Node E) (D : Geometry F) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) => (p.1.1,p.2.fst)) :=
  continuous_fst.fst.prodMk ((outerProjection (E:=E) (F:=F) m).continuous.comp continuous_snd)

omit [CompleteSpace E] [CompleteSpace F] in
theorem innerData_continuous (m : ℕ) (M : Node E) (D : Geometry F) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) => (p.1.2,padded p.2.snd)) :=
  continuous_fst.snd.prodMk ((padded_continuous m).comp
    ((innerProjection (E:=E) (F:=F) m).continuous.comp continuous_snd))

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualOuterSelector_data_continuous (m : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (i : Fin (M.n+1)) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) =>
      virtualOuterSelector M rM p.1.1 i p.2.fst) := by
  exact Continuous.comp
    (f := fun p : HierarchyData M D × Joint E (Blocks m F) => (p.1.1,p.2.fst))
    (g := fun p : (Fin (M.n+1) → E) × E => virtualOuterSelector M rM p.1 i p.2)
    (virtualOuterSelector_continuous M rM i) (macroData_continuous m M D)

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualOuterCarrier_continuous (m : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (d t : ℕ) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) =>
      virtualOuterCarrier m M D rM r p.1.1 p.1.2 d t p.2) := by
  unfold virtualOuterCarrier
  apply continuous_finset_sum
  intro i _
  apply (virtualOuterSelector_data_continuous m M D rM i).mul
  exact Continuous.comp
    (f := fun p : HierarchyData M D × Joint E (Blocks m F) => (p.1.2,padded p.2.snd))
    (g := fun p : ColumnData D × (ℕ → F) => virtualCarrier D r p.1 d 0 [i.val] t p.2)
    (virtualCarrier_continuous D r d 0 [i.val] t) (innerData_continuous m M D)

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualOuterLeaf_continuous (m : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (leaf : ∀ j I,Space (D j I).n → ℝ)
    (hl : ∀ j I,Continuous (leaf j I)) (d : ℕ) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) =>
      virtualOuterLeaf m M D rM r p.1.1 p.1.2 leaf d p.2) := by
  unfold virtualOuterLeaf
  apply continuous_finset_sum
  intro i _
  apply (virtualOuterSelector_data_continuous m M D rM i).mul
  exact Continuous.comp
    (f := fun p : HierarchyData M D × Joint E (Blocks m F) => (p.1.2,padded p.2.snd))
    (g := fun p : ColumnData D × (ℕ → F) => virtualSelect D r p.1 leaf d 0 [i.val] p.2)
    (virtualSelect_continuous D r leaf hl d 0 [i.val]) (innerData_continuous m M D)

omit [CompleteSpace E] [CompleteSpace F] in
theorem virtualCoarse_continuous (m : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (J : ℕ) (i : Fin J) :
    Continuous (fun p : HierarchyData M D × Joint E (Blocks m F) =>
      virtualCoarse m M D rM r p.1.1 p.1.2 J i p.2) := by
  unfold virtualCoarse
  split_ifs
  · exact (virtualOuterCarrier_continuous m M D rM r J J).sub
      (virtualOuterLeaf_continuous m M D rM r (frontierLeaf D)
        (fun j I => (ChiFine.frontier_contDiff (D j I).n (D j I).ell (D j I).width).continuous) J)
  · exact virtualOuterCarrier_continuous m M D rM r J (i.val+1)

end Bilevel.ChiPrefixEvaluation
