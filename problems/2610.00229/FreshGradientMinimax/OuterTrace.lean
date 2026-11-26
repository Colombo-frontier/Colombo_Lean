import FreshGradientMinimax.ProgramMemory
import FreshGradientMinimax.OuterCost

/-! A single original-query program retains all coarse outputs. Every
stored coordinate has exactly the already analysed outer marginal. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev OuterTrace (dx dy : ℕ) := ℕ → Euclid dx × Joint dx dy

def outerTraceProgram (dx dy : ℕ) (L σ μ η Ec Ew : ℝ) : ℕ →
    OracleProgram dx dy (OuterTrace dx dy) (OuterTrace dx dy)
  | 0 => OracleProgram.pure id measurable_id
  | n + 1 => (outerTraceProgram dx dy L σ μ η Ec Ew n).chain
      ((outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n)).recordStep n)

def outerTraceLaw {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) : Measure (OuterTrace dx dy) :=
  (outerTraceProgram dx dy L σ μ η Ec Ew n).resultKernel K ∘ₘ Measure.dirac 0

instance outerTraceLaw_probability {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (outerTraceLaw L σ μ η Ec Ew K n) := by unfold outerTraceLaw; infer_instance

theorem outerTraceLaw_zero {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : outerTraceLaw L σ μ η Ec Ew K 0 = Measure.dirac 0 := by
  rw [outerTraceLaw, outerTraceProgram, OracleProgram.pure_result,
    Measure.deterministic_comp_eq_map measurable_id, Measure.map_id]

theorem outerTraceLaw_succ {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    outerTraceLaw L σ μ η Ec Ew K (n + 1) =
      ((outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n)).recordStep n).resultKernel K ∘ₘ
        outerTraceLaw L σ μ η Ec Ew K n := by
  rw [outerTraceLaw, outerTraceProgram, OracleProgram.chain_result, ← Measure.comp_assoc]
  rfl

theorem outerTraceLaw_coordinate {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n k : ℕ) (hk : k ≤ n) :
    (outerTraceLaw L σ μ η Ec Ew K n).map (fun t => t k) = outerRunLaw L σ μ η Ec Ew K k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    rw [outerTraceLaw_zero, outerRunLaw_zero, Measure.map_dirac (measurable_pi_apply 0)]
    rfl
  | succ n ih =>
    by_cases he : k = n + 1
    · subst k
      rw [outerTraceLaw_succ, OracleProgram.recordStep_new_law, ih n le_rfl, outerRunLaw_succ]
    · rw [outerTraceLaw_succ, OracleProgram.recordStep_old_law _ n k he]
      exact ih k (by omega)

theorem outerTraceProgram_original_coordinate {dx dy : ℕ} (L σ μ η Ec Ew : ℝ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n k : ℕ) (hk : k ≤ n) :
    ((outerTraceProgram dx dy L σ μ η Ec Ew n).originalKernel K ∘ₘ Measure.dirac 0).map
      (fun t => t.1 k) = outerRunLaw L σ μ η Ec Ew K k := by
  have h := outerTraceLaw_coordinate L σ μ η Ec Ew K n k hk
  rw [outerTraceLaw, ← OracleProgram.original_result_law,
    Measure.map_map (measurable_pi_apply k) measurable_fst] at h
  exact h

namespace NCObjective
variable {dx dy : ℕ} {L μ σ : ℝ} (F : NCObjective dx dy L μ)

theorem outerTraceProgram_cost (O : FreshOracle F σ) (η Ec Ew : ℝ) (n : ℕ) (t : OuterTrace dx dy) :
    Integrable costValue ((outerTraceProgram dx dy L σ μ η Ec Ew n).lawKernel O.kernel t) ∧
    (∫ p, costValue p ∂(outerTraceProgram dx dy L σ μ η Ec Ew n).lawKernel O.kernel t) =
      outerRunWork L σ μ η Ec Ew n := by
  induction n with
  | zero =>
    rw [outerTraceProgram, OracleProgram.pure_law]
    exact ⟨taggedKernel_cost_integrable _ _ _, by
      simpa only [outerRunWork, Finset.range_zero, Finset.sum_empty, Nat.cast_zero] using
        taggedKernel_mean_cost (Kernel.deterministic id measurable_id) 0 t⟩
  | succ n ih =>
    have hs (r : OuterTrace dx dy) := F.outerStepProgram_cost O η (outerStageEnvelope Ec Ew n) (r n)
    have hm (r : OuterTrace dx dy) := (outerStepProgram dx dy L σ μ η (outerStageEnvelope Ec Ew n)).recordStep_cost
      n O.kernel r (hs r).1
    rw [outerTraceProgram, OracleProgram.chain_law]
    have h := costedCompose_cost _ _ t ih.1 (fun r => (hm r).1) _
      (fun r => (hm r).2.trans (hs r).2)
    simpa only [ih.2, outerRunWork, Finset.sum_range_succ] using h

end NCObjective
end FreshGradientMinimax
