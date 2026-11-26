import Bilevel.PrimitiveQueryModel

/-! A single public solver with actual expected-risk and original-call
certificates supplies a minimax upper bound in the same query model. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.PrimitiveQuery
set_option autoImplicit false
variable {μ L ρ Δ R₀ σf σg : ℝ}

theorem complexity_le_of_solver (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ)
    (A : Solver) (hA : Accurate C ε A) (B : ℝ≥0∞)
    (hcost : ∀ G (I : Instance G μ L ρ Δ R₀ σf σg),C G I → I.cost (A G)≤B) :
    Complexity C ε≤B := by
  apply iInf_le_of_le ⟨A,hA⟩
  apply iSup_le
  intro I
  exact hcost I.val.1 I.val.2 I.property

end Bilevel.PrimitiveQuery
