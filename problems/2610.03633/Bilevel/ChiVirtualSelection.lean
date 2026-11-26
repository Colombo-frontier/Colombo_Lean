import Bilevel.ChiVirtualRecursion
import Bilevel.ChiVirtualInclusion
import Bilevel.ChiCarrierFineSelection

/-! Actual finite selected leaves under zero-auxiliary restriction. The
leaf is arbitrary, so the same exact identity covers all actual fine atoms,
centered frontiers, and fixed inactive residual replacements. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
variable {E A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]

def virtualSelect (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E)
    (leaf : ∀ j I,Space (D j I).n → ℝ) : ℕ → ℕ → List ℕ → (ℕ → E) → ℝ
  | 0,j,I,u => leaf j I (readout (D j I).n (r j I) (D j I).radius (columns j I) (u j))
  | d+1,j,I,u => ∑ i : Fin ((D j I).n+1),virtualSelector (D j I) (r j I) (columns j I) i (u j)*
      virtualSelect D r columns leaf d (j+1) (child I i.val) u

theorem completed_jointSelector (m j : ℕ) (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E)
    (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ a b : Fin (D.n+1),a.val<r → b.val<r → ⟪columns a,columns b⟫=if a=b then 1 else 0)
    (i : Fin (D.n+1)) (x : Blocks m E) :
    jointSelector m j (completedNode D r columns V hGram) i (blockInclusion m x)=
      virtualSelector D r columns i (block m j x) := by
  change (completedNode D r columns V hGram).selector i (block m j (blockInclusion m x))=_
  rw [block_blockInclusion,completedNode_selector]

theorem completed_select_restriction (m : ℕ) (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] A)
    (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
      ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)
    (leaf : ∀ j I,Space (D j I).n → ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    selectFamily m (completedGeometry D r columns V hGram)
      (fun k P y => leaf k P ((completedGeometry D r columns V hGram k P).coordinates (block m k y)))
      d j I (blockInclusion m x)=virtualSelect D r columns leaf d j I (padded x) := by
  induction d generalizing j I with
  | zero =>
    simp only [selectFamily,virtualSelect,completedGeometry,block_blockInclusion,completedNode_coordinates,padded]
  | succ d ih =>
    simp only [selectFamily,virtualSelect,completedGeometry,completed_jointSelector,ih,padded]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ih (j+1) (child I i.val)

theorem completed_jointCarrier_restriction (m : ℕ) (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] A)
    (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
      ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)
    (d j : ℕ) (I : List ℕ) (k : ℕ) (x : Blocks m E) :
    jointCarrier m (completedGeometry D r columns V hGram) d j I k (blockInclusion m x)=
      virtualCarrier D r columns d j I k (padded x) := by
  have he : padded (blockInclusion (A:=A) m x)=fun j => pack (padded x j) 0 := by
    funext j
    exact block_blockInclusion m j x
  rw [jointCarrier,he,completed_carrier_restriction]

end Bilevel.ChiPrefixEvaluation
