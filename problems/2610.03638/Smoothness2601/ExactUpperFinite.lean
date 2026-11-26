import Smoothness2601.ExactUpperModel
import Smoothness2601.FiniteBudgets

/-! Finite-list class inclusions preserve the exact-upper oracle restriction. -/
noncomputable section
namespace Smoothness2601.ExactUpper

theorem finite_budgetWorks_mono {b : Budgets} {p : ℕ} {L K : ℕ → ℝ}
    {ε : ℝ} {N : ℕ} (hLK : ∀ j, 2 ≤ j → j ≤ p+1 → L j ≤ K j)
    (h : BudgetWorks b p K ε N) : BudgetWorks b p L ε N := by
  intro dx dy
  obtain ⟨A,hA⟩ := h dx dy
  refine ⟨A,?_⟩
  intro P hreg
  apply hA P
  intro q hq hqp x
  have hqp' : q+1 ≤ p := by exact_mod_cast hqp
  obtain ⟨hf,hg,hfb,hgb⟩ := hreg q hq hqp x
  refine ⟨hf,hg,?_,?_⟩
  · intro u v
    exact (hfb u v).trans (mul_le_mul_of_nonneg_right (hLK (q+1) (by omega) (by omega)) (norm_nonneg _))
  · intro u v
    exact (hgb u v).trans (mul_le_mul_of_nonneg_right (hLK (q+2) (by omega) (by omega)) (norm_nonneg _))

theorem minimax_finite_budgets_mono {b : Budgets} {p : ℕ} {L K : ℕ → ℝ} {ε : ℝ}
    (hLK : ∀ j, 2 ≤ j → j ≤ p+1 → L j ≤ K j) :
    minimaxComplexity b p L ε ≤ minimaxComplexity b p K ε := by
  apply sInf_le_sInf
  rintro n ⟨N,rfl,hN⟩
  exact ⟨N,rfl,finite_budgetWorks_mono hLK hN⟩

theorem finite_list_sandwich (b : Budgets) (p : ℕ) (L : ℕ → ℝ)
    (hL : ∀ j, 3 ≤ j → j ≤ p+1 → 0 < L j) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ ε,
      minimaxComplexity b p (derivativeEnvelope b m 1 0) ε ≤
        minimaxComplexity b p (finiteListBudget b L) ε ∧
      minimaxComplexity b p (finiteListBudget b L) ε ≤
        minimaxComplexity b p (derivativeEnvelope b M 1 0) ε := by
  obtain ⟨m,M,hm,hM,hbounds⟩ := finite_list_bounds p L hL
  refine ⟨m,M,hm,hM,fun ε => ⟨?_,?_⟩⟩
  · apply minimax_finite_budgets_mono
    intro j _hj hjp
    by_cases hj2 : j ≤ 2
    · simp [derivativeEnvelope,finiteListBudget,hj2]
    · simpa [derivativeEnvelope,finiteListBudget,hj2] using (hbounds j (by omega) hjp).1
  · apply minimax_finite_budgets_mono
    intro j _hj hjp
    by_cases hj2 : j ≤ 2
    · simp [derivativeEnvelope,finiteListBudget,hj2]
    · simpa [derivativeEnvelope,finiteListBudget,hj2] using (hbounds j (by omega) hjp).2

end Smoothness2601.ExactUpper
