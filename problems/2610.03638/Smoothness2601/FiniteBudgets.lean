import Smoothness2601.Minimax

/-! Class inclusions for an arbitrary positive finite list of higher derivative
budgets. The baseline L₂ budget is kept separate throughout. -/
noncomputable section
namespace Smoothness2601

def finiteListBudget (b : Budgets) (L : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ 2 then b.L₂ else L j

theorem finite_list_bounds (p : ℕ) (L : ℕ → ℝ)
    (hL : ∀ j, 3 ≤ j → j ≤ p+1 → 0 < L j) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ j, 3 ≤ j → j ≤ p+1 → m ≤ L j ∧ L j ≤ M := by
  classical
  let S := insert 1 ((Finset.Icc 3 (p+1)).image L)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hpos : ∀ x ∈ S, (0:ℝ) < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      exact hL j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  refine ⟨S.inf' hS id,S.sup' hS id,?_,?_,?_⟩
  · exact Finset.inf'_induction hS id (fun _ ha _ hb => lt_min ha hb) hpos
  · exact zero_lt_one.trans_le (Finset.le_sup' id (Finset.mem_insert_self _ _))
  · intro j hj hpj
    have hjS : L j ∈ S := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_Icc.mpr ⟨hj,hpj⟩,rfl⟩)
    exact ⟨Finset.inf'_le id hjS,Finset.le_sup' id hjS⟩

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

end Smoothness2601
