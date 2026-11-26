import Bilevel.ChiVirtualNode

/-! Explicit finite-prefix recursive payload and selected carriers.
The completed actual source, restricted to zero auxiliary coordinates,
equals these formulas globally, before any blind-event argument. -/
noncomputable section
open scoped BigOperators
open scoped RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive PrimitiveGeometry
variable {E A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]

def completedGeometry (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E)
    (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] A)
    (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
      ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0) : Geometry (Joint E A) :=
  fun j I => completedNode (D j I) (r j I) (columns j I) (V j I) (hGram j I)

def virtualPayload (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) : ℕ → ℕ → List ℕ → (ℕ → E) → ℝ
  | 0,j,I,u => virtualH (D j I) (r j I) (columns j I) (u j)-virtualH (D j I) (r j I) (columns j I) 0
  | d+1,j,I,u =>
      virtualH (D j I) (r j I) (columns j I) (u j)-
        (∑ i : Fin ((D j I).n+1),virtualResidual (D j I) (r j I) (columns j I) i (u j))+
      (∑ i : Fin ((D j I).n+1),virtualResidual (D j I) (r j I) (columns j I) i (u j)*
        virtualRelease (D (j+1) (child I i.val)) (r (j+1) (child I i.val)) (columns (j+1) (child I i.val)) (u (j+1)))+
      ∑ i : Fin ((D j I).n+1),virtualSelector (D j I) (r j I) (columns j I) i (u j)*
        virtualPayload D r columns d (j+1) (child I i.val) u

def virtualCarrier (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) : ℕ → ℕ → List ℕ → ℕ → (ℕ → E) → ℝ
  | 0,j,I,0,u => virtualH (D j I) (r j I) (columns j I) (u j)-virtualH (D j I) (r j I) (columns j I) 0
  | 0,_,_,_+1,_ => 0
  | _+1,j,I,0,u =>
      virtualH (D j I) (r j I) (columns j I) (u j)-
        (∑ i : Fin ((D j I).n+1),virtualResidual (D j I) (r j I) (columns j I) i (u j))+
      ∑ i : Fin ((D j I).n+1),virtualResidual (D j I) (r j I) (columns j I) i (u j)*
        virtualRelease (D (j+1) (child I i.val)) (r (j+1) (child I i.val)) (columns (j+1) (child I i.val)) (u (j+1))
  | d+1,j,I,k+1,u => ∑ i : Fin ((D j I).n+1),virtualSelector (D j I) (r j I) (columns j I) i (u j)*
      virtualCarrier D r columns d (j+1) (child I i.val) k u

theorem completedNode_H_zero (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (D.n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0) :
    (completedNode D r columns V hGram).H 0=virtualH D r columns 0 :=
  completedNode_H D r columns V hGram 0

theorem completed_payload_restriction (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] A)
    (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
      ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)
    (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    payloadValue (completedGeometry D r columns V hGram) d j I (fun k => pack (u k) 0)=
      virtualPayload D r columns d j I u := by
  induction d generalizing j I with
  | zero => simp only [payloadValue,virtualPayload,completedGeometry,completedNode_H,completedNode_H_zero]
  | succ d ih =>
    simp only [payloadValue,virtualPayload,completedGeometry,completedNode_H,completedNode_residual,
      completedNode_selector,completedNode_release,ih]
    rfl

theorem completed_carrier_restriction (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → E) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] A)
    (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
      ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)
    (d j : ℕ) (I : List ℕ) (k : ℕ) (u : ℕ → E) :
    selectedCarrier (completedGeometry D r columns V hGram) d j I k (fun a => pack (u a) 0)=
      virtualCarrier D r columns d j I k u := by
  induction d generalizing j I k with
  | zero => cases k <;> simp only [selectedCarrier,virtualCarrier,completedGeometry,completedNode_H,completedNode_H_zero]
  | succ d ih =>
    cases k <;> simp only [selectedCarrier,virtualCarrier,completedGeometry,completedNode_H,
      completedNode_residual,completedNode_selector,completedNode_release,ih] <;> rfl

end Bilevel.ChiPrefixEvaluation
