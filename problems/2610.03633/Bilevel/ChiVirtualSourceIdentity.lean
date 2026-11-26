import Bilevel.ChiVirtualHierarchy
import Bilevel.ChiUniformParameterCertificate

/-! Frame completion preserves every source geometric scale exactly. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiOuter PrimitiveGeometry
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]

theorem completed_source_macro (n : ℕ) (initial : Scale) (Km : ℝ)
    (U : Space n →ₗᵢ[ℝ] E) (rM : ℕ) (columns : Fin (n+1) → E) (V : Space n →ₗᵢ[ℝ] A)
    (hGram : ∀ a b : Fin (n+1),a.val<rM → b.val<rM → ⟪columns a,columns b⟫=if a=b then 1 else 0) :
    completedNode (sourceMacroNode n initial Km U) rM columns V hGram=
      sourceMacroNode n initial Km (completionFrame n rM columns V hGram) := rfl

theorem completed_source_geometry (initial : Scale) (ratio resolution weight : ℕ → ℝ)
    (receiver K ζ cn CR : ℝ)
    (frames : ∀ j,List ℕ → Space (sourceChainIndex cn (ratio j) (resolution j)) →ₗᵢ[ℝ] F)
    (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j,List ℕ → Fin (sourceChainIndex cn (ratio j) (resolution j)+1) → F)
    (aux : ∀ j,List ℕ → Space (sourceChainIndex cn (ratio j) (resolution j)) →ₗᵢ[ℝ] B)
    (hGram : ∀ j I,∀ a b : Fin (sourceChainIndex cn (ratio j) (resolution j)+1),
      a.val<r j I → b.val<r j I → ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0) :
    completedGeometry (sourceGeometry initial ratio resolution weight receiver K ζ cn CR frames) r columns aux hGram=
      sourceGeometry initial ratio resolution weight receiver K ζ cn CR
        (fun j I => completionFrame (sourceChainIndex cn (ratio j) (resolution j)) (r j I) (columns j I) (aux j I) (hGram j I)) := rfl

end Bilevel.ChiPrefixEvaluation
