import Bilevel.ChiRecursiveObjective
import Bilevel.ChiRecursiveSourceGeometry

/-! Exact rebasing of the actual recursive tree at an arbitrary outer
prefix. This transports formulas and derivatives, without a new construction. -/
noncomputable section
namespace Bilevel.ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def rebase (D : Geometry E) (P : List ℕ) : Geometry E := fun j I => D j (P++I)

theorem payloadValue_rebase (D : Geometry E) (P : List ℕ) (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    payloadValue (rebase D P) d j I u = payloadValue D d j (P++I) u := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    simp only [payloadValue,rebase,ih,child,List.append_assoc]

theorem objective_rebase (D : Geometry E) (P : List ℕ) (ρ R : ℕ → ℝ)
    (d j : ℕ) (I : List ℕ) (w Rp : ℝ) (u : ℕ → E) :
    objective (rebase D P) ρ R d j I w Rp u = objective D ρ R d j (P++I) w Rp u := by
  simp only [objective,payloadValue_rebase,rebase]

omit [CompleteSpace E] in
theorem sourceGeometry_rebase (initial : Scale) (r η b : ℕ → ℝ) (A K ζ cn CR : ℝ)
    (U : ∀ j,List ℕ → ChiBoundedChain.Space (ChiBoundedChain.sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] E)
    (P : List ℕ) :
    sourceGeometry initial r η b A K ζ cn CR (fun j I => U j (P++I)) =
      rebase (sourceGeometry initial r η b A K ζ cn CR U) P := rfl

end Bilevel.ChiRecursive
