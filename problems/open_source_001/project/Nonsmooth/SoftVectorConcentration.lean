import Nonsmooth.SoftProjectionLimit
import Nonsmooth.SoftWeightMGF
import Nonsmooth.RegularVectorConcentration

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The hard event-conditioned vector inherits centered MGF proxy four from
regular soft approximations. Uncentered exponential integrability is required
only under the original base law. -/
theorem soft_conditioned_vector_concentration (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E)
    (w : ℕ → E → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n z, 0 ≤ w n z ∧ w n z ≤ 1) (hp : ∀ n, ∀ᵐ z ∂μ, 0 < w n z)
    (A : Set E) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun n => w n z) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) z)))
    (H : ∀ n (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → RegularProjectionImage (weightedDensityLaw μ (w n)) u v)
    (v : E) (hExp : Integrable (fun z : E => Real.exp ⟪v, z⟫_ℝ) μ) :
    Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ[|A]⟫_ℝ) μ[|A] ∧
      (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ[|A]⟫_ℝ ∂μ[|A]) ≤ Real.exp (2 * ‖v‖ ^ 2) := by
  letI (n : ℕ) : IsProbabilityMeasure (weightedDensityLaw μ (w n)) :=
    weightedDensityLaw_probability_of_positive μ (w n) (hw n) (hb n) (hp n)
  have hiA : Integrable (fun z : E => z) μ[|A] :=
    (hi.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have hN (n : ℕ) : Integrable (fun z : E => z) (weightedDensityLaw μ (w n)) :=
    integrable_unit_weightedLaw μ _ hi (w n) (hw n) (hb n)
  have hbound (n : ℕ) :
      (∫ z, Real.exp (1 * (⟪v, z⟫_ℝ - ∫ a, ⟪v, a⟫_ℝ ∂weightedDensityLaw μ (w n)))
        ∂weightedDensityLaw μ (w n)) ≤ Real.exp (2 * ‖v‖ ^ 2) := by
    have h := (regular_vector_centered_concentration (weightedDensityLaw μ (w n)) hu hd (H n) v).2
    simpa only [one_mul, integral_inner (hN n), inner_sub_right] using h
  have h := soft_weighted_centered_mgf_bound μ (fun z : E => ⟪v, z⟫_ℝ) (hi.const_inner v) 1
    (by simpa only [one_mul] using hExp) w hw hb A hA hpos hlim (Real.exp (2 * ‖v‖ ^ 2)) hbound
  simpa only [one_mul, integral_inner hiA, inner_sub_right] using h

end
end Nonsmooth
