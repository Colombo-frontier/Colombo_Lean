import FreshGradientMinimax.CostedEpoch
import FreshGradientMinimax.ValueSolver

/-! All epoch cost tags accumulated jointly with the actual value solver.
The output law is unchanged, and the exact expected tag is a finite sum. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def valueSolverWork (ℓ α σ m H e E₀ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (finalEpochIndex E₀ e + 1), fullEpochWork ℓ α σ m H e (valueEnvelope E₀ e j)

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def costedValueRunKernel (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : ℕ → Kernel (Joint dx dy) (Joint dx dy × ℕ)
  | 0 => taggedKernel Kernel.id 0
  | n + 1 => costedCompose (costedValueRunKernel O m H e E₀ r hr n)
      (S.costedFullEpochKernel O m H e (valueEnvelope E₀ e n) r hr)

instance costedValueRunKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) :
    IsMarkovKernel (S.costedValueRunKernel O m H e E₀ r hr n) := by
  induction n with
  | zero => dsimp [costedValueRunKernel]; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (costedCompose (S.costedValueRunKernel O m H e E₀ r hr n) _)
    infer_instance

theorem costedValueRunKernel_first (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) :
    (S.costedValueRunKernel O m H e E₀ r hr n).map Prod.fst = S.valueRunKernel O m H e E₀ r hr n := by
  induction n with
  | zero => exact taggedKernel_first _ _
  | succ n ih => rw [costedValueRunKernel, costedCompose_first, S.costedFullEpochKernel_first, ih, valueRunKernel]

theorem costedValueRunKernel_cost (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) (z : Joint dx dy) :
    Integrable costValue (S.costedValueRunKernel O m H e E₀ r hr n z) ∧
    (∫ t, costValue t ∂S.costedValueRunKernel O m H e E₀ r hr n z) =
      ∑ j ∈ Finset.range n, fullEpochWork ℓ α σ m H e (valueEnvelope E₀ e j) := by
  induction n with
  | zero =>
    refine ⟨taggedKernel_cost_integrable _ _ _, ?_⟩
    simpa only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero] using
      taggedKernel_mean_cost (Kernel.id : Kernel (Joint dx dy) (Joint dx dy)) 0 z
  | succ n ih =>
    have h := costedCompose_cost (S.costedValueRunKernel O m H e E₀ r hr n)
      (S.costedFullEpochKernel O m H e (valueEnvelope E₀ e n) r hr) z ih.1
      (fun t => (S.costedFullEpochKernel_cost O m H e (valueEnvelope E₀ e n) r hr t).1) _
      (fun t => (S.costedFullEpochKernel_cost O m H e (valueEnvelope E₀ e n) r hr t).2)
    simpa only [ih.2, Finset.sum_range_succ] using h

def costedValueSolverKernel (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : Kernel (Joint dx dy) (Joint dx dy × ℕ) :=
  S.costedValueRunKernel O m H e E₀ r hr (finalEpochIndex E₀ e + 1)

instance costedValueSolverKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    IsMarkovKernel (S.costedValueSolverKernel O m H e E₀ r hr) := by unfold costedValueSolverKernel; infer_instance

theorem costedValueSolverKernel_first (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (S.costedValueSolverKernel O m H e E₀ r hr).map Prod.fst = S.valueSolverKernel O m H e E₀ r hr :=
  S.costedValueRunKernel_first O m H e E₀ r hr _

theorem costedValueSolverKernel_output_law (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (ν : Measure (Joint dx dy)) :
    (S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν).map Prod.fst =
      S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν := by
  rw [Measure.map_comp _ _ measurable_fst, S.costedValueSolverKernel_first]

theorem costedValueSolverKernel_cost (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (z : Joint dx dy) :
    Integrable costValue (S.costedValueSolverKernel O m H e E₀ r hr z) ∧
    (∫ t, costValue t ∂S.costedValueSolverKernel O m H e E₀ r hr z) = valueSolverWork ℓ α σ m H e E₀ :=
  S.costedValueRunKernel_cost O m H e E₀ r hr _ z

theorem costedValueSolverKernel_random_cost (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν] :
    Integrable costValue (S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) ∧
    (∫ t, costValue t ∂S.costedValueSolverKernel O m H e E₀ r hr ∘ₘ ν) = valueSolverWork ℓ α σ m H e E₀ := by
  have h (z : Joint dx dy) := S.costedValueSolverKernel_cost O m H e E₀ r hr z
  have hi := (kernel_moment_from_envelope (S.costedValueSolverKernel O m H e E₀ r hr) ν costValue
    costValue_measurable.stronglyMeasurable (fun t => Nat.cast_nonneg t.2)
    (fun _ => valueSolverWork ℓ α σ m H e E₀) (integrable_const _) (fun z => (h z).1)
    (fun z => (h z).2.le)).1
  refine ⟨hi, ?_⟩
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi, Kernel.const_apply]
  simp_rw [(h _).2]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]

end SCObjective
end FreshGradientMinimax
