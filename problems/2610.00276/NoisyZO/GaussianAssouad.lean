import NoisyZO.GaussianAdaptiveSum

/-!
# Assouad testing for the concrete adaptive Gaussian transcript law

This module removes the abstract edge-KL hypothesis from the lower-bound
assembly.  The KL divergence is now that of the recursively constructed
finite transcript laws, and its total budget is supplied by
`adaptive_gaussian_edge_KL_total_bound`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NoisyZO

/-- Assouad--Pinsker applied directly to the finite adaptive Gaussian laws.

`err` and `tv` retain their decision-theoretic meaning.  The two assumptions
`hedge` and `hpinsker` are the standard testing inequality and Pinsker
inequality, respectively; all Gaussian transcript and averaging work is
discharged in the conclusion. -/
theorem adaptive_gaussian_assouad_bound
    {α : Type*} [MeasurableSpace α] {d T : ℕ} (hd : 0 < d)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (mean : Hypercube d → ℕ → α → ℝ)
    (hmean : ∀ s t, Measurable (mean s t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (hint : ∀ s i t,
      Integrable (fun a ↦
        (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2)
        (adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate t))
    (C : ℝ) (hC : 0 ≤ C)
    (hsignal : ∀ s (t : Fin T) a,
      ∑ i : Fin d,
        (mean s t a - mean (flipHypercube s i) t a) ^ 2 ≤ C)
    (err tv : Hypercube d → Fin d → ℝ)
    (hedge : ∀ s i,
      1 - tv s i ≤ err s i + err (flipHypercube s i) i)
    (hpinsker : ∀ s i,
      tv s i ≤ Real.sqrt
        ((InformationTheory.klDiv
          (adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate T)
          (adaptiveGaussianLaw μ₀ (mean (flipHypercube s i))
            (hmean (flipHypercube s i)) update hupdate T)).toReal / 2)) :
    ((((2 : ℝ) ^ d * d) / 2) *
        (1 - Real.sqrt ((T * C / (2 * d)) / 2))) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
  let P : Hypercube d → Measure α := fun s ↦
    adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate T
  let KL : Hypercube d → Fin d → ℝ := fun s i ↦
    (InformationTheory.klDiv (P s) (P (flipHypercube s i))).toReal
  have hKLnonneg : ∀ s i, 0 ≤ KL s i := by
    intro s i
    exact ENNReal.toReal_nonneg
  have htotal :
      (∑ s : Hypercube d, ∑ i : Fin d, KL s i) ≤
        (2 : ℝ) ^ d * T * C / 2 := by
    simpa only [KL, P] using
      adaptive_gaussian_edge_KL_total_bound μ₀ mean hmean update hupdate hint C hsignal
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hbudget :
      (∑ s : Hypercube d, ∑ i : Fin d, KL s i) ≤
        ((2 : ℝ) ^ d * d) * (T * C / (2 * d)) := by
    calc
      (∑ s : Hypercube d, ∑ i : Fin d, KL s i) ≤
          (2 : ℝ) ^ d * T * C / 2 := htotal
      _ = ((2 : ℝ) ^ d * d) * (T * C / (2 * d)) := by
        field_simp [ne_of_gt hdR]
  have hKbar : 0 ≤ T * C / (2 * d) := by positivity
  apply assouad_pinsker_bound err tv KL (T * C / (2 * d))
    hKbar hKLnonneg hedge
  · intro s i
    simpa only [KL, P] using hpinsker s i
  · exact hbudget

end NoisyZO
