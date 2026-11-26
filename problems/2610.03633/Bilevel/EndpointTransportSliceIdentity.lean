import Bilevel.EndpointTransportNormalExtension
import Bilevel.EndpointTransportCoarseCarriers

/-! Exact fixed-macro slices of the actual physical hierarchy. These are
pointwise identities of the constructed functions, before any support or
derivative claim. The physical source and target maps are retained. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiLiftedCarrier
open ChiRecursive ChiCarrier
variable {E X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem selectFamily_congr_inputs {m : ℕ} (G : Geometry E)
    (A : X →L[ℝ] Blocks m E) (B : Y →L[ℝ] Blocks m E)
    (f : ℕ → List ℕ → X → ℝ) (g : ℕ → List ℕ → Y → ℝ)
    (x : X) (y : Y) (hxy : A x=B y) (hf : ∀ k I,f k I x=g k I y)
    (d j : ℕ) (I : List ℕ) :
    selectFamily m G A f d j I x=selectFamily m G B g d j I y := by
  induction d generalizing j I with
  | zero => exact hf j I
  | succ d ih =>
    simp only [selectFamily,selector,Function.comp_apply,hxy,ih]

end Bilevel.ChiLiftedCarrier
namespace Bilevel.EndpointTransportResponse
open ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre
variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem physicalCarrier_congr_inputs {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (A' : Y →L[ℝ] Blocks m (Block D)) (B' : Y →L[ℝ] Physical n D)
    (x : X) (y : Y) (hA : A x=A' y) (hB : B x=B' y)
    (d j : ℕ) (I : List ℕ) (t : ℕ) :
    physicalCarrier m Q G A B d j I t x=physicalCarrier m Q G A' B' d j I t y := by
  induction d generalizing j I t with
  | zero => cases t <;> simp only [physicalCarrier,hB]
  | succ d ih =>
    cases t with
    | zero =>
      simp only [physicalCarrier,lastParentCarrier,physicalReleaseCorrection,hA,hB]
    | succ t =>
      simp only [physicalCarrier,ChiLiftedCarrier.selector,Function.comp_apply,hA,ih]

theorem selectedPhysicalFinePiece_congr_inputs {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (A' : Y →L[ℝ] Blocks m (Block D)) (B' : Y →L[ℝ] Physical n D)
    (x : X) (y : Y) (hA : A x=A' y) (hB : B x=B' y)
    (P : ChiFine.Parameters) (p d j : ℕ) (I : List ℕ) :
    selectedPhysicalFinePiece m G A B Q P p d j I x=
      selectedPhysicalFinePiece m G A' B' Q P p d j I y := by
  exact ChiLiftedCarrier.selectFamily_congr_inputs G A A' _ _ x y hA
    (fun k I => congrArg (physicalFinePiece Q (G k I) P p) hB) d j I

theorem selectedPhysicalFineFrontier_congr_inputs {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (A' : Y →L[ℝ] Blocks m (Block D)) (B' : Y →L[ℝ] Physical n D)
    (x : X) (y : Y) (hA : A x=A' y) (hB : B x=B' y)
    (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) :
    selectedPhysicalFineFrontier m G A B Q P d j I x=
      selectedPhysicalFineFrontier m G A' B' Q P d j I y := by
  exact ChiLiftedCarrier.selectFamily_congr_inputs G A A' _ _ x y hA
    (fun k I => congrArg (physicalFineFrontier Q (G k I) P) hB) d j I

theorem physicalCoarseCarrier_congr_inputs {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (A' : Y →L[ℝ] Blocks m (Block D)) (B' : Y →L[ℝ] Physical n D)
    (x : X) (y : Y) (hA : A x=A' y) (hB : B x=B' y)
    (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (t : ℕ) :
    physicalCoarseCarrier m Q G A B P d j I t x=physicalCoarseCarrier m Q G A' B' P d j I t y := by
  simp only [physicalCoarseCarrier,physicalCarrier_congr_inputs Q G A B A' B' x y hA hB,
    selectedPhysicalFineFrontier_congr_inputs Q G A B A' B' x y hA hB]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem outerPhysicalCoarseCarrier_eq_sum {m n D : ℕ} (Q : Rotations n D) (M : Node E)
    (macroP : X →L[ℝ] E) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d t : ℕ) (x : X) :
    outerPhysicalCoarseCarrier m Q M macroP G A B P d t x=
      ∑ i : Fin (M.n+1),macroSelector M macroP i x*physicalCoarseCarrier m Q G A B P d 0 [i.val] t x := by
  by_cases ht : t=d
  · simp only [outerPhysicalCoarseCarrier,outerPhysicalCarrier,outerPhysicalFineFrontier,
      macroSelected,physicalCoarseCarrier,if_pos ht,mul_sub,Finset.sum_sub_distrib]
  · simp only [outerPhysicalCoarseCarrier,outerPhysicalCarrier,macroSelected,physicalCoarseCarrier,
      if_neg ht,sub_zero]

theorem physicalHierarchyCoarse_slice {n D J : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (i : Fin J) (a : E)
    (x : HybridTangent (Blocks J (Block D)) n D) :
    physicalHierarchyCoarse Q M G P J i (pack a x)=
      ∑ l : Fin (M.n+1),wrappedSelector M l a*
        physicalCoarseCarrier J Q G jointFstLinear jointSndLinear P J 0 [l.val] (i.val+1) x := by
  rw [physicalHierarchyCoarse,outerPhysicalCoarseFamily,outerPhysicalCoarseCarrier_eq_sum]
  apply Finset.sum_congr rfl
  intro l _
  change wrappedSelector M l a*_=_
  rw [physicalCoarseCarrier_congr_inputs Q G _ _ jointFstLinear jointSndLinear (pack a x) x rfl rfl]

theorem physicalHierarchyFine_piece_slice {n D J : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (p : ℕ) (a : E)
    (x : HybridTangent (Blocks J (Block D)) n D) :
    (physicalHierarchyFine Q M G P J).e p (pack a x)=
      ∑ l : Fin (M.n+1),wrappedSelector M l a*
        selectedPhysicalFinePiece J G jointFstLinear jointSndLinear Q P p J 0 [l.val] x := by
  change (∑ l : Fin (M.n+1),macroSelector M (baseMacroProjection J n D) l (pack a x)*
    selectedPhysicalFinePiece J G (baseOrdinaryProjection J n D) (basePhysicalProjection J n D)
      Q P p J 0 [l.val] (pack a x))=_
  apply Finset.sum_congr rfl
  intro l _
  change wrappedSelector M l a*_=_
  rw [selectedPhysicalFinePiece_congr_inputs Q G _ _ jointFstLinear jointSndLinear (pack a x) x rfl rfl]

end Bilevel.EndpointTransportResponse
