import Smoothness2601.StoppingPadding
import Smoothness2601.UniformMinimax

/-! The source at-most-N convention is equivalent to exact-N minimax.
Stopping uses arbitrary public memory; that memory can include a clock, all
observations, and a private random tape. Every active position costs one
original sample, stopped positions cost none, and output occurs by position N. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601

def StoppedBudgetWorks (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) (N : ℕ) : Prop :=
  ∀ dx dy : ℕ, ∃ A : Adaptive.Algorithm (Euclidean dx) (Euclidean dy),
    ∃ halt : A.Memory → Bool, ∃ hh : Measurable halt,
      ∀ P : Population (X := Euclidean dx) (Y := Euclidean dy) b,
        P.HigherRegularity p L → ∀ x₀ y₀, P.Initialized x₀ y₀ →
        ∀ (H : Type) (inst : MeasurableSpace H), letI := inst
          ∀ (O : Adaptive.Oracle P H) (h : H),
            (∫⁻ x, (‖gradient P.objective x‖₊ : ℝ≥0∞)
              ∂StoppingPadding.stoppedOutput A halt hh O N h (x₀,y₀)) ≤ ENNReal.ofReal ε

theorem stoppedBudgetWorks_iff {b : Budgets} {p : WithTop ℕ} {L : ℕ → ℝ} {ε : ℝ} {N : ℕ} :
    StoppedBudgetWorks b p L ε N ↔ BudgetWorks b p L ε N := by
  constructor
  · intro h dx dy
    obtain ⟨A,halt,hh,hA⟩ := h dx dy
    refine ⟨StoppingPadding.padded A halt hh (true,0,0),?_⟩
    intro P hreg x₀ y₀ hi H inst O history
    unfold Adaptive.Succeeds Adaptive.expectedNorm
    rw [StoppingPadding.padding_output]
    exact hA P hreg x₀ y₀ hi H inst O history
  · intro h dx dy
    obtain ⟨A,hA⟩ := h dx dy
    refine ⟨A,(fun _ => false),measurable_const,?_⟩
    intro P hreg x₀ y₀ hi H inst O history
    have he := StoppingPadding.padding_output A (fun _ => false) measurable_const O (true,0,0) N history
    rw [StoppingPadding.padded_never] at he
    rw [← he]
    exact hA P hreg x₀ y₀ hi H inst O history

def stoppedMinimaxComplexity (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  sInf {n | ∃ N : ℕ, n = (N : ℝ≥0∞) ∧ StoppedBudgetWorks b p L ε N}

theorem stopped_minimax_eq (b : Budgets) (p : WithTop ℕ) (L : ℕ → ℝ) (ε : ℝ) :
    stoppedMinimaxComplexity b p L ε = minimaxComplexity b p L ε := by
  simp only [stoppedMinimaxComplexity,minimaxComplexity,stoppedBudgetWorks_iff]

/-- The main theorem with bounded, memory-dependent stopping explicitly
allowed. Padding is proved above; no stopping-model equivalence is assumed. -/
theorem uniform_minimax_atMost (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) :
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧
      ∀ p : WithTop ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ENNReal.ofReal (c*ε^(-4:ℝ)*orderTradeoff p β ε^2) ≤
          stoppedMinimaxComplexity b p (derivativeEnvelope b M Λ β) ε ∧
        stoppedMinimaxComplexity b p (derivativeEnvelope b M Λ β) ε ≤
          ENNReal.ofReal (C*ε^(-4:ℝ)*orderTradeoff p β ε^2) := by
  simp_rw [stopped_minimax_eq]
  exact uniform_minimax b hgap hM hΛ hβ

end Smoothness2601
