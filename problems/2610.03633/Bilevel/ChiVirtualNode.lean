import Bilevel.ChiPrefixCompletion
import Bilevel.ChiRecursivePayload

/-! Actual source nodes completed in an auxiliary block and their explicit
finite-prefix scalar formulas. The formulas use no undisclosed frame data. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive PrimitiveGeometry
variable {E A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]

def completedNode (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (D.n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0) :
    Node (Joint E A) where
  n := D.n
  ell := D.ell
  width := D.width
  receiver := D.receiver
  nu := D.nu
  force := D.force
  parentWidth := D.parentWidth
  tailRadius := D.tailRadius
  radius := D.radius
  frame := completionFrame D.n r columns V hGram

def virtualH (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (u : E) : ℝ :=
  payload D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
    (readout D.n r D.radius columns u)

def virtualSelector (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (i : Fin (D.n+1)) (u : E) : ℝ :=
  selector D.n i (D.width⁻¹ • readout D.n r D.radius columns u)

def virtualResidual (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (i : Fin (D.n+1)) (u : E) : ℝ :=
  Rterm D.n D.ell D.width i (readout D.n r D.radius columns u)

def virtualRelease (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (u : E) : ℝ :=
  releaseGate (readout D.n r D.radius columns u (Fin.last D.n)/D.parentWidth)

theorem completedNode_coordinates (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (D.n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (u : E) : (completedNode D r columns V hGram).coordinates (pack u 0)=readout D.n r D.radius columns u :=
  completion_coordinates D.n r D.radius columns V hGram u

theorem completedNode_H (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (D.n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (u : E) : (completedNode D r columns V hGram).H (pack u 0)=virtualH D r columns u := by
  unfold Node.H virtualH
  rw [completedNode_coordinates]
  rfl

theorem completedNode_selector (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (D.n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (i : Fin (D.n+1)) (u : E) :
    (completedNode D r columns V hGram).selector i (pack u 0)=virtualSelector D r columns i u := by
  unfold Node.selector virtualSelector
  rw [completedNode_coordinates]
  rfl

theorem completedNode_residual (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (D.n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (i : Fin (D.n+1)) (u : E) :
    (completedNode D r columns V hGram).residual i (pack u 0)=virtualResidual D r columns i u := by
  unfold Node.residual virtualResidual
  rw [completedNode_coordinates]
  rfl

theorem completedNode_release (D : Node E) (r : ℕ) (columns : Fin (D.n+1) → E) (V : Space D.n →ₗᵢ[ℝ] A)
    (hGram : ∀ i j : Fin (D.n+1),i.val<r → j.val<r → ⟪columns i,columns j⟫=if i=j then 1 else 0)
    (u : E) : (completedNode D r columns V hGram).release (pack u 0)=virtualRelease D r columns u := by
  unfold Node.release virtualRelease
  rw [completedNode_coordinates]
  rfl

end Bilevel.ChiPrefixEvaluation
