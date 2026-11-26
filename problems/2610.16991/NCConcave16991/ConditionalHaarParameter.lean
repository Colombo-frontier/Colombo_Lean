import NCConcave16991.ConditionalHaarTail
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lifting actual Haar probability bounds through independent parameters

The other rotations and a policy's private seed may be collected into any
probability space. Fubini lifts a uniform actual Haar fibre bound to the
product law. No countability or topological assumption on the seed is used.
-/

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Haar

noncomputable section

theorem independent_parameter_event_bound {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {s : Set (Ω × OrthogonalGroup k)} (hs : MeasurableSet s) {b : ℝ}
    (hbound : ∀ ω, (haarLaw k).real (Prod.mk ω ⁻¹' s) ≤ b) :
    (ν.prod (haarLaw k)).real s ≤ b := by
  have hint : Integrable (s.indicator (fun _ ↦ (1:ℝ))) (ν.prod (haarLaw k)) :=
    (integrable_const (1:ℝ)).indicator hs
  have hpoint (ω : Ω) :
      ∫ Q, s.indicator (fun _ ↦ (1:ℝ)) (ω,Q) ∂haarLaw k = (haarLaw k).real (Prod.mk ω ⁻¹' s) := by
    have he : (fun Q ↦ s.indicator (fun _ ↦ (1:ℝ)) (ω,Q)) =
        (Prod.mk ω ⁻¹' s).indicator (fun _ ↦ (1:ℝ)) := rfl
    rw [he, integral_indicator_const (1:ℝ) (hs.preimage measurable_prodMk_left)]
    simp only [smul_eq_mul, mul_one]
  calc
    _ = ∫ z, s.indicator (fun _ ↦ (1:ℝ)) z ∂ν.prod (haarLaw k) := by
      rw [integral_indicator_const (1:ℝ) hs]
      simp only [smul_eq_mul, mul_one]
    _ = ∫ ω, ∫ Q, s.indicator (fun _ ↦ (1:ℝ)) (ω,Q) ∂haarLaw k ∂ν := integral_prod _ hint
    _ ≤ ∫ _ : Ω, b ∂ν := integral_mono_ae hint.integral_prod_left (integrable_const b)
      (Filter.Eventually.of_forall (fun ω ↦ (hpoint ω).trans_le (hbound ω)))
    _ = b := by simp

/-- An arbitrary independent seed and other hidden rotations may influence the
probe. Only its Haar section must be measurable from that section's revealed
columns. -/
theorem independent_parameter_observed_inner_tail {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A : Finset (Fin k))
    (a : Ω → OrthogonalGroup k → EuclideanSpace ℝ (Fin k))
    (hjoint : Measurable (Function.uncurry a))
    (ha : ∀ ω, StronglyMeasurable[columnSigma A] (a ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ ω Q, ‖a ω Q‖ ≤ C)
    (j : Fin k) (hj : j ∉ A) {r : ℝ} (hr : 0 < r) :
    (ν.prod (haarLaw k)).real {z | r ≤ |⟪a z.1 z.2,
      orthogonalLinearIsometryEquiv z.2 (basisVector j)⟫_ℝ|} ≤
      C ^ 2 / ((Aᶜ.card : ℝ) * r ^ 2) := by
  have hinner : Measurable (fun z : Ω × OrthogonalGroup k ↦
      ⟪a z.1 z.2, orthogonalLinearIsometryEquiv z.2 (basisVector j)⟫_ℝ) :=
    hjoint.inner ((continuous_orthogonalLinearIsometryEquiv_apply (basisVector j)).measurable.comp measurable_snd)
  apply independent_parameter_event_bound ν
    (measurableSet_le measurable_const (continuous_abs.measurable.comp hinner))
  intro ω
  exact observed_inner_tail A (a ω) (ha ω) hC (hb ω) j hj hr

end

end NCConcave16991.Haar
