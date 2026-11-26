import FreshGradientMinimax.OuterComplete
import FreshGradientMinimax.ProgramSuccess
import FreshGradientMinimax.Minimax

/-! An explicit finite deterministic budget suffices for the localized
class in the nontrivial parameter regime. The algorithm is chosen before
the objective and oracle; logarithmic simplification of this budget is separate. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def refinedOuterBudget (L σ μ Δ G ε : ℝ) : ℕ := ⌈12 * (1 + refinedOuterWork L σ μ Δ G ε)⌉₊

def localizedBudgetMethod (dx dy : ℕ) (L σ μ Δ G ε : ℝ) (hT : 0 < outerStepCount L Δ ε) :
    RandomizedAlgorithm dx dy :=
  (refinedOuterProgram dx dy L σ μ Δ G ε hT).budgetMethod (fun p => p.2.1) measurable_snd.fst 0

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem localizedBudgetMethod_success (O : FreshOracle F σ) {Δ G ε : ℝ}
    (hΔ : F.PrimalGapAtMost Δ) (hG : F.DualLocalized G) (hε : 0 < ε) (hreg : ε ^ 2 ≤ L * Δ)
    (hT : 0 < outerStepCount L Δ ε) :
    5 / 6 ≤ ((localizedBudgetMethod dx dy L σ μ Δ G ε hT).outputLaw O.kernel
      (refinedOuterBudget L σ μ Δ G ε)).real (F.successSet ε) := by
  have hc := F.refinedOuterProgram_mean_calls O Δ G ε hT
  have he := F.refinedOuterProgram_gradient_accuracy O hΔ hG hε hreg hT
  rw [Measure.dirac_bind (Kernel.measurable _)] at hc he
  have hw : 0 ≤ refinedOuterWork L σ μ Δ G ε := by
    rw [← hc.2]
    exact integral_nonneg (fun p => Nat.cast_nonneg p.2)
  have hg : Measurable (gradient F.value) := by
    have heq : gradient F.value = F.primalGradient := funext F.true_primal_gradient
    rw [heq]
    exact F.primalGradient_continuous.measurable
  exact (refinedOuterProgram dx dy L σ μ Δ G ε hT).budgetMethod_success
    (fun p : Euclid dx × Joint dx dy => p.2.1) measurable_snd.fst (0 : OuterTrace dx dy) O.kernel
    (gradient F.value) hg (N := refinedOuterBudget L σ μ Δ G ε)
    (by linarith : 0 < 1 + refinedOuterWork L σ μ Δ G ε) hε
    (Nat.le_ceil _) hc.1 (by linarith [hc.2]) he.1 he.2

end NCObjective

theorem localized_budget_explicit (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    BudgetSuffices p (some p.G) (refinedOuterBudget p.L p.σ p.μ p.gap p.G p.ε) := by
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  have hΔ : 0 < p.gap := by nlinarith [sq_pos_of_pos p.ε_pos]
  have hT := outerStepCount_pos hL hΔ p.ε_pos
  intro dx dy
  refine ⟨localizedBudgetMethod dx dy p.L p.σ p.μ p.gap p.G p.ε hT, ?_⟩
  intro F O hc
  have h := F.localizedBudgetMethod_success O hc.1 hc.2 p.ε_pos hreg hT
  exact le_trans (by norm_num : (2 : ℝ) / 3 ≤ 5 / 6) h

theorem localized_complexity_explicit (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    localizedComplexity p ≤ (refinedOuterBudget p.L p.σ p.μ p.gap p.G p.ε : ℕ∞) :=
  complexity_le_of_budget (localized_budget_explicit p hreg)

end FreshGradientMinimax
