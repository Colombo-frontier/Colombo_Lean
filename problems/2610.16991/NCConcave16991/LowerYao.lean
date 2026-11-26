import Mathlib.MeasureTheory.Measure.Prod

/-! # The actual product-law contradiction for randomized lower bounds

The success sections need not form a jointly measurable event. It suffices
that they lie in sections of a measurable observable bad event.
-/

open MeasureTheory Set
open scoped ENNReal

namespace NCConcave16991

variable {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
  (ν : Measure Θ) (μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

theorem prior_seed_bad_mass_lower (B : Set (Θ × Ω)) (hB : MeasurableSet B)
    (S : Θ → Set Ω) {q : ℝ≥0∞}
    (hprob : ∀ θ, q ≤ μ (S θ)) (hsub : ∀ θ, S θ ⊆ {ω | (θ, ω) ∈ B}) :
    q ≤ (ν.prod μ) B := by
  rw [Measure.prod_apply hB]
  calc
    q = ∫⁻ _θ, q ∂ν := by simp
    _ ≤ ∫⁻ θ, μ (Prod.mk θ ⁻¹' B) ∂ν :=
      lintegral_mono (fun θ ↦ (hprob θ).trans (measure_mono (hsub θ)))

theorem seed_prior_bad_mass_lower (B : Set (Ω × Θ)) (hB : MeasurableSet B)
    (S : Θ → Set Ω) {q : ℝ≥0∞}
    (hprob : ∀ θ, q ≤ μ (S θ)) (hsub : ∀ θ, S θ ⊆ {ω | (ω, θ) ∈ B}) :
    q ≤ (μ.prod ν) B := by
  rw [Measure.prod_apply_symm hB]
  calc
    q = ∫⁻ _θ, q ∂ν := by simp
    _ ≤ ∫⁻ θ, μ ((fun ω ↦ (ω, θ)) ⁻¹' B) ∂ν :=
      lintegral_mono (fun θ ↦ (hprob θ).trans (measure_mono (hsub θ)))

theorem seed_prior_uniform_success_contradiction (B : Set (Ω × Θ)) (hB : MeasurableSet B)
    (S : Θ → Set Ω) {q : ℝ≥0∞}
    (hprob : ∀ θ, q ≤ μ (S θ)) (hsub : ∀ θ, S θ ⊆ {ω | (ω, θ) ∈ B})
    (hsmall : (μ.prod ν) B < q) : False :=
  (not_le_of_gt hsmall) (seed_prior_bad_mass_lower ν μ B hB S hprob hsub)

theorem seed_prior_exists_failure (B : Set (Ω × Θ)) (hB : MeasurableSet B)
    (S : Θ → Set Ω) {q : ℝ≥0∞} (hsub : ∀ θ, S θ ⊆ {ω | (ω, θ) ∈ B})
    (hsmall : (μ.prod ν) B < q) : ∃ θ, μ (S θ) < q := by
  by_contra h
  have hp : ∀ θ, q ≤ μ (S θ) := fun θ ↦ le_of_not_gt (fun ht ↦ h ⟨θ, ht⟩)
  exact seed_prior_uniform_success_contradiction ν μ B hB S hp hsub hsmall

end NCConcave16991
