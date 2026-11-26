import Smoothness2601.Minimax

/-! Conversion of genuine fixed-budget obstructions to the minimax infimum.
The obstruction itself is an explicit premise here; this module does not
claim to construct a hard population. -/
noncomputable section
open scoped ENNReal
namespace Smoothness2601

/-- Excluding every integer budget below a real threshold proves the
corresponding minimax lower bound, including when the feasible set is empty. -/
theorem minimax_lower_of_budget_obstruction {b : Budgets} {p : WithTop ℕ}
    {L : ℕ → ℝ} {ε threshold : ℝ}
    (h : ∀ N : ℕ, (N : ℝ) < threshold → ¬ BudgetWorks b p L ε N) :
    ENNReal.ofReal threshold ≤ minimaxComplexity b p L ε := by
  apply le_sInf
  rintro n ⟨N,rfl,hN⟩
  have hh : threshold ≤ (N : ℝ) := le_of_not_gt (fun hn => h N hn hN)
  exact_mod_cast ENNReal.ofReal_le_ofReal hh

end Smoothness2601
