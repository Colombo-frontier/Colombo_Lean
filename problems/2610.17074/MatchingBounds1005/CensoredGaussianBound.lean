import MatchingBounds1005.CensoredGaussianProcess
import MatchingBounds1005.HistoryPath

/-!
# Telescoped KL bound for the actual censored transcript

Each hidden signal is present until its disclosure time along the realized
history. The proved innovation energy telescoping removes any factor equal
to the number of queries. The geometric bounds on the final pre-disclosure
projections remain explicit hypotheses for the separate Haar/tensor layer.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal

namespace MatchingBounds1005.CensoredGaussianBound
open GaussianVector CensoredGaussianProcess HistoryPath

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

theorem energyCost_eq (A : CensoredProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (h : SequentialPosterior.History Ω T n) :
    energyCost A σ n h =
      ‖InnovationEnergy.proj (innovation A n h) (hidden A n h)‖ ^ 2 / (2 * σ ^ 2) := rfl

attribute [local irreducible] InnovationEnergy.proj Submodule.orthogonalProjection

theorem innovation_path (A : CensoredProtocol Ω d T) (seed : Ω)
    (answers : ℕ → Fin T → ℝ) (n : ℕ) :
    innovation A n (path seed answers n) =
      pathExposure A.original.rowProtocol seed answers (n + 1) ⊓
        (pathExposure A.original.rowProtocol seed answers n)ᗮ := by
  rw [innovation_eq]
  rfl

/-- Exact finite-history energy telescoping for signals removed once. -/
theorem path_energy_sum_le (A : CensoredProtocol Ω d T) (σ : ℝ)
    (seed : Ω) (answers : ℕ → Fin T → ℝ) {ι : Type*} (signals : Finset ι)
    (f : ι → Vec d) (w : ℝ) (ell : ι → ℕ) (N : ℕ)
    (hell : ∀ s ∈ signals, ell s ≤ N)
    (hhidden : ∀ k < N, hidden A k (path seed answers k) =
      w • ∑ s ∈ signals, if k < ell s then f s else 0) :
    (∑ k ∈ Finset.range N, energyCost A σ k (path seed answers k)) ≤
      (signals.card : ℝ) * w ^ 2 *
        (∑ s ∈ signals,
          ‖InnovationEnergy.proj (pathExposure A.original.rowProtocol seed answers (ell s)) (f s)‖ ^ 2) /
        (2 * σ ^ 2) := by
  have heq : (∑ k ∈ Finset.range N, energyCost A σ k (path seed answers k)) =
      (∑ k ∈ Finset.range N,
        ‖InnovationEnergy.proj
          (pathExposure A.original.rowProtocol seed answers (k + 1) ⊓
            (pathExposure A.original.rowProtocol seed answers k)ᗮ)
          (w • ∑ s ∈ signals, if k < ell s then f s else 0)‖ ^ 2) / (2 * σ ^ 2) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [energyCost_eq, innovation_path, hhidden k (Finset.mem_range.mp hk)]
  rw [heq]
  exact div_le_div_of_nonneg_right
    (InnovationEnergy.cumulative_hidden_signal_energy signals
      (pathExposure A.original.rowProtocol seed answers)
      (pathExposure_monotone A.original.rowProtocol seed answers) f w ell N hell)
    (by positivity)

/-- Actual reference-versus-static-transcript KL with no query-count loss.
`B` bounds the sum of the final pre-disclosure projection energies. No KL,
posterior identity, or change-of-measure bound is assumed. -/
theorem transcript_klDiv_le (A : CensoredProtocol Ω d T) {σ : ℝ} (hσ : σ ≠ 0)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (C : ℕ → ℝ≥0)
    (hc : ∀ n h, ‖hidden A n h‖ ^ 2 / (2 * σ ^ 2) ≤ C n)
    {ι : Type*} (signals : Finset ι) (f : Ω → ι → Vec d) (w : ℝ)
    (ell : Ω → (ℕ → Fin T → ℝ) → ι → ℕ) (N : ℕ) (B : ℝ)
    (hell : ∀ seed answers s, s ∈ signals → ell seed answers s ≤ N)
    (hhidden : ∀ seed answers k, k < N → hidden A k (path seed answers k) =
      w • ∑ s ∈ signals, if k < ell seed answers s then f seed s else 0)
    (henergy : ∀ seed answers,
      (∑ s ∈ signals,
        ‖InnovationEnergy.proj
          (pathExposure A.original.rowProtocol seed answers (ell seed answers s)) (f seed s)‖ ^ 2) ≤ B) :
    klDiv (referenceLaw A σ ν₀ N) (trueLaw A σ ν₀ N) ≤
      ENNReal.ofReal ((signals.card : ℝ) * w ^ 2 * B / (2 * σ ^ 2)) := by
  apply CensoredGaussianProcess.transcript_klDiv_le A hσ ν₀ C hc N
  intro h
  apply cumulativeCost_le_of_path _ N _ ?_ h
  intro seed answers
  exact (path_energy_sum_le A σ seed answers signals (f seed) w (ell seed answers) N
    (hell seed answers) (hhidden seed answers)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (henergy seed answers)
          (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg w))) (by positivity))

end MatchingBounds1005.CensoredGaussianBound
