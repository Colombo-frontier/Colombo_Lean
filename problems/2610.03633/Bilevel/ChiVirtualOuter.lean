import Bilevel.ChiVirtualHierarchy

/-! Explicit outer-selected disclosed-data formulas. These definitions do
not inspect any undisclosed frame column or any proof of prefix validity. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

def virtualOuterSelector (M : Node E) (rM : ℕ) (columns : Fin (M.n+1) → E)
    (i : Fin (M.n+1)) (u : E) : ℝ :=
  ChiOuter.selector M.n i (M.width⁻¹ • readout M.n rM M.radius columns u)

def tangentialInclusion (m : ℕ) : Joint E (Blocks m F) →ₗᵢ[ℝ]
    Joint (Joint E A) (Blocks m (Joint F B)) :=
  jointMap zeroInclusion (blockInclusion m)

theorem completed_outerSelector (M : Node E) (rM : ℕ) (columns : Fin (M.n+1) → E)
    (V : Space M.n →ₗᵢ[ℝ] A)
    (hGram : ∀ a b : Fin (M.n+1),a.val<rM → b.val<rM →
      ⟪columns a,columns b⟫=if a=b then 1 else 0)
    (i : Fin (M.n+1)) (u : E) :
    wrappedSelector (completedNode M rM columns V hGram) i (pack u 0)=
      virtualOuterSelector M rM columns i u := by
  unfold wrappedSelector virtualOuterSelector
  rw [completedNode_coordinates]
  rfl

def virtualOuterCarrier (m : ℕ) (M : Node E) (D : Geometry F) (rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (d t : ℕ)
    (z : Joint E (Blocks m F)) : ℝ :=
  ∑ i : Fin (M.n+1),virtualOuterSelector M rM macroColumns i z.fst *
    virtualCarrier D r columns d 0 [i.val] t (padded z.snd)

def virtualOuterLeaf (m : ℕ) (M : Node E) (D : Geometry F) (rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (leaf : ∀ j I,Space (D j I).n → ℝ) (d : ℕ) (z : Joint E (Blocks m F)) : ℝ :=
  ∑ i : Fin (M.n+1),virtualOuterSelector M rM macroColumns i z.fst *
    virtualSelect D r columns leaf d 0 [i.val] (padded z.snd)

variable (m : ℕ) (M : Node E) (D : Geometry F) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
  (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
  (VM : Space M.n →ₗᵢ[ℝ] A) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] B)
  (hmGram : ∀ a b : Fin (M.n+1),a.val<rM → b.val<rM →
    ⟪macroColumns a,macroColumns b⟫=if a=b then 1 else 0)
  (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
    ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)

theorem completed_outerCarrier_restriction (d t : ℕ) (z : Joint E (Blocks m F)) :
    outerCarrier m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) d t (tangentialInclusion m z)=
      virtualOuterCarrier m M D rM r macroColumns columns d t z := by
  unfold outerCarrier outerSelected virtualOuterCarrier
  apply Finset.sum_congr rfl
  intro i _
  change wrappedSelector (completedNode M rM macroColumns VM hmGram) i (pack z.fst 0) *
    jointCarrier m (completedGeometry D r columns V hGram) d 0 [i.val] t (blockInclusion m z.snd)=_
  rw [completed_outerSelector,completed_jointCarrier_restriction]

theorem completed_outerLeaf_restriction (leaf : ∀ j I,Space (D j I).n → ℝ)
    (d : ℕ) (z : Joint E (Blocks m F)) :
    outerSelected m (completedNode M rM macroColumns VM hmGram)
      (fun i => selectFamily m (completedGeometry D r columns V hGram)
        (fun j I x => leaf j I ((completedGeometry D r columns V hGram j I).coordinates (block m j x)))
        d 0 [i.val]) (tangentialInclusion m z)=
      virtualOuterLeaf m M D rM r macroColumns columns leaf d z := by
  unfold outerSelected virtualOuterLeaf
  apply Finset.sum_congr rfl
  intro i _
  change wrappedSelector (completedNode M rM macroColumns VM hmGram) i (pack z.fst 0) *
    selectFamily m (completedGeometry D r columns V hGram)
      (fun j I x => leaf j I ((completedGeometry D r columns V hGram j I).coordinates (block m j x)))
      d 0 [i.val] (blockInclusion m z.snd)=_
  rw [completed_outerSelector,completed_select_restriction]

end Bilevel.ChiPrefixEvaluation
