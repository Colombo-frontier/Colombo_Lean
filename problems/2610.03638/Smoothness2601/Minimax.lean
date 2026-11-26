import Smoothness2601.AdaptiveModel
import Smoothness2601.OrderTradeoff

/-! The article's minimax quantifiers, using the kernel execution model.
UniformMinimax proves the rate proposition defined below. Randomized execution
uses arbitrary private memory and history-dependent conditional-moment kernels.
StoppingPadding proves exact output-law equivalence with bounded early stopping;
StoppedMinimax transfers the minimax quantity to the at-most-N convention. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The baseline L₂ budget remains separate from the factorial envelope. -/
def derivativeEnvelope (b : Budgets) (M Λ β : ℝ) (j : ℕ) : ℝ :=
  if j ≤ 2 then b.L₂ else M * Λ ^ j * (j.factorial : ℝ) ^ β

/-- One algorithm per known dimension, uniformly for all admissible populations,
starting points, and history-dependent oracle laws. N counts original samples.
The algorithm is not given a population function or its minimizer. -/
def BudgetWorks (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) (N : ℕ) : Prop :=
  ∀ dx dy : ℕ, ∃ A : Adaptive.Algorithm (Euclidean dx) (Euclidean dy),
    ∀ P : Population (X := Euclidean dx) (Y := Euclidean dy) b,
    P.HigherRegularity p L → ∀ x₀ y₀, P.Initialized x₀ y₀ →
    ∀ (H : Type) (inst : MeasurableSpace H), letI := inst
      ∀ (O : Adaptive.Oracle P H) (h : H), Adaptive.Succeeds A O N ε h x₀ y₀

/-- Infinite value means that no finite uniformly successful budget exists. -/
def minimaxComplexity (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  sInf {n | ∃ N : ℕ, n = (N : ℝ≥0∞) ∧ BudgetWorks b p L ε N}

theorem minimax_le_budget {b : Budgets} {p : WithTop ℕ} {L : ℕ → ℝ} {ε : ℝ} {N : ℕ}
    (hN : BudgetWorks b p L ε N) : minimaxComplexity b p L ε ≤ N :=
  sInf_le ⟨N, rfl, hN⟩

theorem budget_accuracy_mono {b : Budgets} {p : WithTop ℕ} {L : ℕ → ℝ}
    {ε δ : ℝ} {N : ℕ} (h : BudgetWorks b p L ε N) (hεδ : ε ≤ δ) :
    BudgetWorks b p L δ N := by
  intro dx dy
  obtain ⟨A,hA⟩ := h dx dy
  refine ⟨A, ?_⟩
  intro P hp x₀ y₀ hi H inst O h
  exact (hA P hp x₀ y₀ hi H inst O h).trans (ENNReal.ofReal_le_ofReal hεδ)

theorem budget_smoothness_mono {b : Budgets} {p : WithTop ℕ} {L K : ℕ → ℝ}
    {ε : ℝ} {N : ℕ} (hLK : ∀ j, L j ≤ K j) (h : BudgetWorks b p K ε N) :
    BudgetWorks b p L ε N := by
  intro dx dy
  obtain ⟨A,hA⟩ := h dx dy
  refine ⟨A, ?_⟩
  intro P hp
  exact hA P (P.higherRegularity_mono_budgets hLK hp)

theorem budget_order_mono {b : Budgets} {p r : WithTop ℕ} {L : ℕ → ℝ}
    {ε : ℝ} {N : ℕ} (hpr : p ≤ r) (h : BudgetWorks b p L ε N) :
    BudgetWorks b r L ε N := by
  intro dx dy
  obtain ⟨A,hA⟩ := h dx dy
  refine ⟨A, ?_⟩
  intro P hp
  exact hA P (P.higherRegularity_mono_order hpr hp)

theorem minimax_smoothness_mono {b : Budgets} {p : WithTop ℕ} {L K : ℕ → ℝ}
    {ε : ℝ} (hLK : ∀ j, L j ≤ K j) :
    minimaxComplexity b p L ε ≤ minimaxComplexity b p K ε := by
  apply sInf_le_sInf
  rintro n ⟨N,rfl,hN⟩
  exact ⟨N,rfl,budget_smoothness_mono hLK hN⟩

/-- The main rate proposition `thm:uniform`, proved by `uniform_minimax` in
UniformMinimax. DimensionHardFamily and the source oracle lemmas certify the
scalar, dimension, exact-upper, and two-fixed-loss hard-instance clauses. -/
def UniformMinimaxClaim (b : Budgets) (M Λ β : ℝ) : Prop :=
  ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧
    ∀ p : WithTop ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ENNReal.ofReal (c * ε ^ (-4 : ℝ) * orderTradeoff p β ε ^ 2) ≤
        minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ∧
      minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ≤
        ENNReal.ofReal (C * ε ^ (-4 : ℝ) * orderTradeoff p β ε ^ 2)

end Smoothness2601
