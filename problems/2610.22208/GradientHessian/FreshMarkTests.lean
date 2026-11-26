import GradientHessian.Shadow

/-! Product-law integration for fresh tests, allowing the test to depend on
all previous data. The fresh parameter retains its original probability law. -/

namespace GradientHessian.FreshMarkTests
open MeasureTheory
noncomputable section

theorem independent_hit_bound {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (μ : Measure H) [IsProbabilityMeasure μ] (ν : Measure Z) [IsProbabilityMeasure ν]
    (hit : H → Z → Prop) (hmeas : MeasurableSet {t : H × Z | hit t.1 t.2})
    {p : ℝ} (hp : 0 ≤ p) (hpoint : ∀ᵐ h ∂μ, ν.real {z | hit h z} ≤ p) :
    (μ.prod ν).real {t : H × Z | hit t.1 t.2} ≤ p := by
  have he : (μ.prod ν) {t : H × Z | hit t.1 t.2} ≤ ENNReal.ofReal p := by
    rw [Measure.prod_apply hmeas]
    calc
      _ ≤ ∫⁻ _h, ENNReal.ofReal p ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with h hh
        change ν {z | hit h z} ≤ ENNReal.ofReal p
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal hh
      _ = _ := by simp
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [measureReal_def, ENNReal.toReal_ofReal hp] using h

/-- A finite collection chosen from the earlier-data coordinate incurs only
the explicit number of tests in the union bound. -/
theorem independent_list_bound {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (μ : Measure H) [IsProbabilityMeasure μ] (ν : Measure Z) [IsProbabilityMeasure ν]
    (N : ℕ) (hit : Fin N → H → Z → Prop)
    (hmeas : ∀ i, MeasurableSet {t : H × Z | hit i t.1 t.2})
    {p : ℝ} (hp : 0 ≤ p) (hpoint : ∀ i, ∀ᵐ h ∂μ, ν.real {z | hit i h z} ≤ p) :
    (μ.prod ν).real {t : H × Z | ∃ i, hit i t.1 t.2} ≤ N * p := by
  have he : {t : H × Z | ∃ i, hit i t.1 t.2} = ⋃ i, {t : H × Z | hit i t.1 t.2} := by
    ext t
    simp
  rw [he]
  calc
    _ ≤ ∑ i, (μ.prod ν).real {t : H × Z | hit i t.1 t.2} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin N, p := Finset.sum_le_sum (fun i _ =>
      independent_hit_bound μ ν (hit i) (hmeas i) hp (hpoint i))
    _ = N * p := by simp

end
end GradientHessian.FreshMarkTests
