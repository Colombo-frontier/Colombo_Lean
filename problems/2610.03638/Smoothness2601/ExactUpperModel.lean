import Smoothness2601.ExactUpperOracle

/-! Unrestricted adaptive minimax with the additional oracle restriction that
every upper full-gradient response is exact. The algorithm is chosen first. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601.ExactUpper

def BudgetWorks (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) (N : ℕ) : Prop :=
  ∀ dx dy : ℕ, ∃ A : Adaptive.Algorithm (Euclidean dx) (Euclidean dy),
    ∀ P : Population (X := Euclidean dx) (Y := Euclidean dy) b,
    P.HigherRegularity p L → ∀ x₀ y₀, P.Initialized x₀ y₀ →
    ∀ (H : Type) (inst : MeasurableSpace H), letI := inst
      ∀ (O : Adaptive.Oracle P H), IsExact P O → ∀ h : H, Adaptive.Succeeds A O N ε h x₀ y₀

def minimaxComplexity (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  sInf {n | ∃ N : ℕ, n = (N:ℝ≥0∞) ∧ BudgetWorks b p L ε N}

theorem budgetWorks_of_full {b : Budgets} {p : WithTop ℕ} {L : ℕ → ℝ} {ε : ℝ} {N : ℕ}
    (hN : Smoothness2601.BudgetWorks b p L ε N) : BudgetWorks b p L ε N := by
  intro dx dy
  obtain ⟨A,hA⟩ := hN dx dy
  refine ⟨A,?_⟩
  intro P hreg x₀ y₀ hi H inst O _hO h
  exact hA P hreg x₀ y₀ hi H inst O h

theorem minimax_le_full (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) :
    minimaxComplexity b p L ε ≤ Smoothness2601.minimaxComplexity b p L ε := by
  apply sInf_le_sInf
  rintro n ⟨N,rfl,hN⟩
  exact ⟨N,rfl,budgetWorks_of_full hN⟩

theorem minimax_lower_of_budget_obstruction {b : Budgets} {p : WithTop ℕ}
    {L : ℕ → ℝ} {ε threshold : ℝ}
    (h : ∀ N : ℕ, (N:ℝ) < threshold → ¬BudgetWorks b p L ε N) :
    ENNReal.ofReal threshold ≤ minimaxComplexity b p L ε := by
  apply le_sInf
  rintro n ⟨N,rfl,hN⟩
  have hh : threshold ≤ (N:ℝ) := le_of_not_gt (fun hn => h N hn hN)
  exact_mod_cast ENNReal.ofReal_le_ofReal hh

theorem budgetWorks_scalar {b : Budgets} {p : WithTop ℕ} {L : ℕ → ℝ} {ε : ℝ} {N : ℕ}
    (hN : BudgetWorks b p L ε N) :
    ∀ dx : ℕ, ∃ A : Adaptive.Algorithm (Euclidean dx) ℝ,
      ∀ P : Population (X := Euclidean dx) (Y := ℝ) b,
      P.HigherRegularity p L → ∀ x₀ y₀, P.Initialized x₀ y₀ →
      ∀ (H : Type) (inst : MeasurableSpace H), letI := inst
        ∀ (O : Adaptive.Oracle P H), IsExact P O → ∀ h : H, Adaptive.Succeeds A O N ε h x₀ y₀ := by
  intro dx
  obtain ⟨A,hA⟩ := hN dx 1
  let e := CoordinateMinimax.scalarEquiv
  refine ⟨CoordinateAlgorithm.pull A e,?_⟩
  intro P hreg x₀ y₀ hi H inst O hO h
  apply CoordinateAlgorithm.succeeds A e P O N ε h x₀ y₀
  exact hA (CoordinatePopulation.transport P e)
    (CoordinatePopulation.higherRegularity P e hreg)
    x₀ (e.symm y₀) (CoordinatePopulation.initialized P e hi)
    H inst (CoordinateOracle.transport P e O) (coordinate_transport P e O hO) h

end Smoothness2601.ExactUpper
