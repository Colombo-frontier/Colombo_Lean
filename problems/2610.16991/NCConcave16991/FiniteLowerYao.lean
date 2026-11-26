import NCConcave16991.LowerYao
import NCConcave16991.ConditionalHaarProduct
import NCConcave16991.DenseWeakProductBank

/-! # Finite hard families: section measurability suffices for the actual Yao contradiction -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NCConcave16991

variable {Θ Ω : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [MeasurableSpace Ω]

theorem finite_success_relation_measurable (S : Θ → Set Ω) (hS : ∀ θ, MeasurableSet (S θ)) :
    MeasurableSet {z : Ω × Θ | z.1 ∈ S z.2} := by
  classical
  have he : {z : Ω × Θ | z.1 ∈ S z.2} =
      ⋃ θ, {z : Ω × Θ | z.1 ∈ S θ ∧ z.2 = θ} := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hz
      exact ⟨z.2,hz,rfl⟩
    · rintro ⟨θ,hz,hθ⟩
      simpa only [hθ] using hz
  rw [he]
  exact MeasurableSet.iUnion (fun θ ↦
    ((hS θ).preimage measurable_fst).inter (measurable_snd (measurableSet_singleton θ)))

/-- Arbitrary private seed spaces are permitted; the proof only integrates
the genuine finite hard-family success sections supplied by the valid policy. -/
theorem finite_prior_uniform_success_contradiction
    (prior : DenseWeakHiding.FiniteLaw Θ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Θ → Set Ω) (hS : ∀ θ, MeasurableSet (S θ)) {q : ℝ≥0∞} (hq : q ≠ ⊤)
    (hprob : ∀ θ, q ≤ μ (S θ)) {c : ℝ} (hc : c < q.toReal)
    (hupper : ∀ ω, prior.law.real {θ | ω ∈ S θ} ≤ c) : False := by
  let B : Set (Ω × Θ) := {z | z.1 ∈ S z.2}
  have hB : MeasurableSet B := finite_success_relation_measurable S hS
  have hlow := seed_prior_bad_mass_lower prior.law μ B hB S hprob (fun _ ↦ fun _ h ↦ h)
  have hlowR := ENNReal.toReal_mono (measure_ne_top (μ.prod prior.law) B) hlow
  have hu : (μ.prod prior.law).real B ≤ c := Haar.product_event_bound μ prior.law hB hupper
  change q.toReal ≤ (μ.prod prior.law).real B at hlowR
  linarith

end NCConcave16991
