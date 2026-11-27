import Nonsmooth.SoftWeightLimits
import Nonsmooth.ContinuousRank

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

theorem soft_weighted_measure_real_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 1)
    (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)))
    (B : Set α) (hB : MeasurableSet B) :
    Tendsto (fun n => (weightedDensityLaw μ (w n)).real B) atTop (𝓝 ((μ[|A]).real B)) := by
  have h := soft_weighted_law_integral_tendsto μ (B.indicator (fun _ => (1 : ℝ)))
    ((integrable_const _).indicator hB) w hw hb A hA hpos hlim
  simpa only [integral_indicator hB, integral_const, measureReal_def, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one] using h

/-- Distribution functions of every measurable scalar observation converge
under bounded positive soft weights approaching an event indicator. -/
theorem soft_weighted_cdf_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 1) (hp : ∀ n, ∀ᵐ x ∂μ, 0 < w n x)
    (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)))
    (X : α → ℝ) (hX : Measurable X) (y : ℝ) :
    Tendsto (fun n => cdf ((weightedDensityLaw μ (w n)).map X) y) atTop (𝓝 (cdf ((μ[|A]).map X) y)) := by
  letI (n : ℕ) : IsProbabilityMeasure (weightedDensityLaw μ (w n)) :=
    weightedDensityLaw_probability_of_positive μ (w n) (hw n) (hb n) (hp n)
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hpos
  letI (n : ℕ) : IsProbabilityMeasure ((weightedDensityLaw μ (w n)).map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure ((μ[|A]).map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have h := soft_weighted_measure_real_tendsto μ w hw hb A hA hpos hlim
    (X ⁻¹' Iic y) (hX measurableSet_Iic)
  simpa only [cdf_eq_real, map_measureReal_apply hX measurableSet_Iic] using h

end
end Nonsmooth
