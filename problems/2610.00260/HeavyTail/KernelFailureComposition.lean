import HeavyTail.AdaptiveKernelOutputKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Failure propagation through genuine Markov transition laws. A stage
guarantee is required only at good preceding centers. Its failure probability
is added to the mass of bad centers, with no independence assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HeavyTail

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem kernel_failure_propagation (μ : Measure X) [IsProbabilityMeasure μ]
    (K : Kernel X Y) [IsMarkovKernel K] (bad : Set X) (hbad : MeasurableSet bad)
    (nextBad : Set Y) (hnext : MeasurableSet nextBad) (ε : ℝ≥0∞)
    (hstep : ∀ x ∉ bad, K x nextBad ≤ ε) :
    (K ∘ₘ μ) nextBad ≤ μ bad + ε := by
  rw [Measure.bind_apply hnext K.aemeasurable]
  calc
    _ ≤ ∫⁻ x, bad.indicator (fun _ => (1 : ℝ≥0∞)) x + ε ∂μ := by
      apply lintegral_mono
      intro x
      change K x nextBad ≤ bad.indicator (fun _ => (1 : ℝ≥0∞)) x + ε
      by_cases hx : x ∈ bad
      · rw [indicator_of_mem hx]
        have hp : K x nextBad ≤ 1 := (measure_mono (subset_univ nextBad)).trans_eq (measure_univ)
        exact hp.trans (le_add_right le_rfl)
      · rw [indicator_of_not_mem hx, zero_add]
        exact hstep x hx
    _ = μ bad + ε := by
      rw [lintegral_add_left (measurable_const.indicator hbad), lintegral_indicator hbad]
      simp

def stageKernelLaw (K : ℕ → Kernel X X) (μ : Measure X) : ℕ → Measure X
  | 0 => μ
  | n + 1 => K n ∘ₘ stageKernelLaw K μ n

instance stageKernelLaw_probability (K : ℕ → Kernel X X)
    [∀ n, IsMarkovKernel (K n)] (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (stageKernelLaw K μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure (K n ∘ₘ stageKernelLaw K μ n)
    infer_instance

theorem stageKernelLaw_failure (K : ℕ → Kernel X X) [∀ n, IsMarkovKernel (K n)]
    (μ : Measure X) [IsProbabilityMeasure μ] (bad : ℕ → Set X)
    (hbad : ∀ n, MeasurableSet (bad n)) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ n x, x ∉ bad n → K n x (bad (n + 1)) ≤ ε n) (N : ℕ) :
    stageKernelLaw K μ N (bad N) ≤ μ (bad 0) + ∑ n ∈ Finset.range N, ε n := by
  induction N with
  | zero => simp [stageKernelLaw]
  | succ N ih =>
    have hs := kernel_failure_propagation (stageKernelLaw K μ N) (K N)
      (bad N) (hbad N) (bad (N + 1)) (hbad (N + 1)) (ε N) (hstep N)
    calc
      _ ≤ stageKernelLaw K μ N (bad N) + ε N := hs
      _ ≤ (μ (bad 0) + ∑ n ∈ Finset.range N, ε n) + ε N := add_le_add_right ih _
      _ = _ := by rw [Finset.sum_range_succ, add_assoc]

theorem stageKernelLaw_failure_bounded (K : ℕ → Kernel X X) [∀ n, IsMarkovKernel (K n)]
    (μ : Measure X) [IsProbabilityMeasure μ] (bad : ℕ → Set X)
    (hbad : ∀ n, MeasurableSet (bad n)) (ε : ℕ → ℝ≥0∞) (N : ℕ)
    (hstep : ∀ j < N, ∀ x ∉ bad j, K j x (bad (j + 1)) ≤ ε j) :
    stageKernelLaw K μ N (bad N) ≤ μ (bad 0) + ∑ j ∈ Finset.range N, ε j := by
  induction N with
  | zero => simp [stageKernelLaw]
  | succ N ih =>
    have hp := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self N)))
    have hs := kernel_failure_propagation (stageKernelLaw K μ N) (K N)
      (bad N) (hbad N) (bad (N + 1)) (hbad (N + 1)) (ε N) (hstep N (Nat.lt_succ_self N))
    calc
      _ ≤ stageKernelLaw K μ N (bad N) + ε N := hs
      _ ≤ (μ (bad 0) + ∑ j ∈ Finset.range N, ε j) + ε N := add_le_add_right hp _
      _ = _ := by rw [Finset.sum_range_succ, add_assoc]

theorem stageKernelLaw_terminal_failure (K : ℕ → Kernel X X) [∀ n, IsMarkovKernel (K n)]
    (μ : Measure X) [IsProbabilityMeasure μ] (bad : ℕ → Set X)
    (hbad : ∀ j, MeasurableSet (bad j)) (ε : ℕ → ℝ≥0∞) (N : ℕ)
    (hstep : ∀ j < N, ∀ x ∉ bad j, K j x (bad (j + 1)) ≤ ε j)
    (terminalBad : Set X) (hterminal : MeasurableSet terminalBad) (δ : ℝ≥0∞)
    (hfinal : ∀ x ∉ bad N, K N x terminalBad ≤ δ) :
    stageKernelLaw K μ (N + 1) terminalBad ≤
      μ (bad 0) + (∑ j ∈ Finset.range N, ε j) + δ := by
  exact (kernel_failure_propagation (stageKernelLaw K μ N) (K N)
    (bad N) (hbad N) terminalBad hterminal δ hfinal).trans
      (add_le_add_right (stageKernelLaw_failure_bounded K μ bad hbad ε N hstep) δ)

end HeavyTail
