import Nonsmooth.WeightedDensityLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α F : Type} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem soft_weighted_integral_tendsto (μ : Measure α) (f : α → F) (hf : Integrable f μ)
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 1)
    (A : Set α) (hA : MeasurableSet A)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x))) :
    Tendsto (fun n => ∫ x, w n x • f x ∂μ) atTop (𝓝 (∫ x in A, f x ∂μ)) := by
  rw [← integral_indicator hA]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · exact fun n => (hw n).aestronglyMeasurable.smul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact Eventually.of_forall (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (hb n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb n x).2)
  · filter_upwards [hlim] with x hx
    have h := hx.smul (tendsto_const_nhds (x := f x))
    convert h using 1
    by_cases hxA : x ∈ A <;> simp [hxA]

/-- Bounded soft weights converging to an event indicator give convergence of
actual normalized vector means, including their changing normalizing masses. -/
theorem soft_weighted_law_integral_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → F) (hf : Integrable f μ)
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 1)
    (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x))) :
    Tendsto (fun n => ∫ x, f x ∂weightedDensityLaw μ (w n)) atTop (𝓝 (∫ x, f x ∂μ[|A])) := by
  have hnum := soft_weighted_integral_tendsto μ f hf w hw hb A hA hlim
  have hden := soft_weighted_integral_tendsto μ (fun _ => (1 : ℝ)) (integrable_const _) w hw hb A hA hlim
  simp only [smul_eq_mul, mul_one, integral_const, measureReal_def, Measure.restrict_apply_univ] at hden
  have hmass : μ.real A ≠ 0 := (ENNReal.toReal_pos hpos (measure_ne_top μ A)).ne'
  have ht := (hden.inv₀ hmass).smul hnum
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  convert ht using 1
  funext n
  exact weightedDensityLaw_integral μ (w n) (hw n)
    (unit_weight_integrable μ (w n) (hw n) (hb n)) (fun x => (hb n x).1) f

end
end Nonsmooth
