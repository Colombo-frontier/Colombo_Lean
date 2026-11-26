import HeavyTail.AdaptiveKernelConcatenation
import HeavyTail.KernelFailureComposition

/-! A finite sequence of genuine causal policies, with deterministic stage
budgets. Exact output laws and failure propagation are proved for the composed
policy, whose seed at each restart is the preceding actual output. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HeavyTail.AdaptiveKernel
universe u v

def stageCalls (budget : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => stageCalls budget N + budget N

theorem stageCalls_eq_sum (budget : ℕ → ℕ) (N : ℕ) :
    stageCalls budget N = ∑ j ∈ Finset.range N, budget j := by
  induction N with
  | zero => simp [stageCalls]
  | succ N ih => simp only [stageCalls, ih, Finset.sum_range_succ]

namespace Policy
variable {Center Reply : Type u} {Query : Type v}
  [MeasurableSpace Center] [MeasurableSpace Reply] [MeasurableSpace Query]

def zeroStage (q : Query) : Policy Center Query Reply Center 0 where
  query _ _ := q
  query_measurable _ := measurable_const
  output := id
  output_measurable := measurable_id

theorem zeroStage_outputLaw (q : Query) (μ : Measure Center) (K : Kernel Query Reply) :
    (zeroStage (Center := Center) q).outputLaw μ K = μ := Measure.map_id

def stages (q : Query) {budget : ℕ → ℕ}
    (A : ∀ j, Policy Center Query Reply Center (budget j)) :
    (N : ℕ) → Policy Center Query Reply Center (stageCalls budget N)
  | 0 => zeroStage q
  | N + 1 => (stages q A N).chain (A N)

theorem stages_outputLaw (q : Query) {budget : ℕ → ℕ}
    (A : ∀ j, Policy Center Query Reply Center (budget j))
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] (N : ℕ) :
    (stages q A N).outputLaw μ K =
      stageKernelLaw (fun j => (A j).outputKernel K) μ N := by
  induction N with
  | zero => exact zeroStage_outputLaw q μ K
  | succ N ih =>
    change ((stages q A N).chain (A N)).outputLaw μ K = _
    rw [chain_outputLaw_kernel, ih]
    rfl

theorem stages_failure (q : Query) {budget : ℕ → ℕ}
    (A : ∀ j, Policy Center Query Reply Center (budget j))
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K]
    (bad : ℕ → Set Center) (hbad : ∀ j, MeasurableSet (bad j)) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ j c, c ∉ bad j → (A j).outputLaw (Measure.dirac c) K (bad (j + 1)) ≤ ε j)
    (N : ℕ) :
    (stages q A N).outputLaw μ K (bad N) ≤ μ (bad 0) + ∑ j ∈ Finset.range N, ε j := by
  rw [stages_outputLaw]
  apply stageKernelLaw_failure _ μ bad hbad ε
  intro j c hc
  rw [outputKernel_apply]
  exact hstep j c hc

end Policy
end HeavyTail.AdaptiveKernel
