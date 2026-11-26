import Bilevel.ChiVirtualOuter

/-! The actual coarse, fine and fixed signal scalars as disclosed-data
formulas, with exact completed-source restriction identities. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtensionCalibration ZeroChainSchedule
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

def frontierLeaf (D : Geometry F) (j : ℕ) (I : List ℕ) : Space (D j I).n → ℝ :=
  ChiFine.frontier (D j I).n (D j I).ell (D j I).width

def pieceLeaf (D : Geometry F) (c θ : ℝ) (p j : ℕ) (I : List ℕ) : Space (D j I).n → ℝ :=
  ZeroChainResidualScaled.scaled (ChiFine.piece (D j I).n (levels θ) (resolution c 1 θ) p)
    ((D j I).ell*(D j I).width^2) (D j I).width

def signalLeaf (D : Geometry F) (τ : ℝ) (j : ℕ) (I : List ℕ) : Space (D j I).n → ℝ :=
  ChiFine.signalResidual (D j I).n (D j I).ell (D j I).width τ

def virtualCoarse (m : ℕ) (M : Node E) (D : Geometry F) (rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (J : ℕ) (i : Fin J)
    (z : Joint E (Blocks m F)) : ℝ :=
  if i.val+1=J then virtualOuterCarrier m M D rM r macroColumns columns J J z-
    virtualOuterLeaf m M D rM r macroColumns columns (frontierLeaf D) J z
  else virtualOuterCarrier m M D rM r macroColumns columns J (i.val+1) z

variable (m : ℕ) (M : Node E) (D : Geometry F) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
  (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
  (VM : Space M.n →ₗᵢ[ℝ] A) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] B)
  (hmGram : ∀ a b : Fin (M.n+1),a.val<rM → b.val<rM →
    ⟪macroColumns a,macroColumns b⟫=if a=b then 1 else 0)
  (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
    ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)

theorem completed_outerFineFrontier_restriction (d : ℕ) (z : Joint E (Blocks m F)) :
    outerFineFrontier m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) d (tangentialInclusion m z)=
      virtualOuterLeaf m M D rM r macroColumns columns (frontierLeaf D) d z :=
  completed_outerLeaf_restriction m M D rM r macroColumns columns VM V hmGram hGram (frontierLeaf D) d z

theorem completed_outerFinePiece_restriction (d : ℕ) (c θ : ℝ) (p : ℕ) (z : Joint E (Blocks m F)) :
    outerFinePiece m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) d c θ p (tangentialInclusion m z)=
      virtualOuterLeaf m M D rM r macroColumns columns (pieceLeaf D c θ p) d z :=
  completed_outerLeaf_restriction m M D rM r macroColumns columns VM V hmGram hGram (pieceLeaf D c θ p) d z

theorem completed_outerSignal_restriction (d : ℕ) (τ : ℝ) (z : Joint E (Blocks m F)) :
    outerFineSignal m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) d τ (tangentialInclusion m z)=
      virtualOuterLeaf m M D rM r macroColumns columns (signalLeaf D τ) d z :=
  completed_outerLeaf_restriction m M D rM r macroColumns columns VM V hmGram hGram (signalLeaf D τ) d z

theorem completed_coarse_restriction (J : ℕ) (i : Fin J) (z : Joint E (Blocks m F)) :
    coarseFamily m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) J i (tangentialInclusion m z)=
      virtualCoarse m M D rM r macroColumns columns J i z := by
  unfold coarseFamily virtualCoarse
  split_ifs
  · unfold outerDeepestA
    rw [completed_outerCarrier_restriction,completed_outerFineFrontier_restriction]
  · exact completed_outerCarrier_restriction m M D rM r macroColumns columns VM V hmGram hGram J (i.val+1) z

end Bilevel.ChiPrefixEvaluation
