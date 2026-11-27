import Nonsmooth.SupportMaximumEntropy

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)]

/-- All lower-tail conditioning costs together have a dimension-free bound.
The row laws may differ; independence enters through the maximum CDF product. -/
theorem maximum_total_lower_tail_cost (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (L : Fin k → ℝ → ℝ) (hL : ∀ i, Measurable (L i))
    (hL0 : ∀ i y, 0 ≤ L i y) {K : ℝ}
    (hb : ∀ i y, 0 < cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y →
      L i y ≤ K * Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)) :
    Integrable (fun y => ∑ i, L i y) (supportResponseLaw μ u) ∧
      (∫ y, ∑ i, L i y ∂supportResponseLaw μ u) ≤ K := by
  have hinfo := supportResponseLaw_total_tail_information μ u hzero
  have hu : (fun y => ∑ i, L i y) ≤ᵐ[supportResponseLaw μ u]
      (fun y => K * ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
    filter_upwards [supportResponseLaw_cdf_positive_ae μ u hzero] with y hy
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hb i y (hy i))
  have hm : Measurable (fun y => ∑ i, L i y) := by fun_prop
  have hi : Integrable (fun y => ∑ i, L i y) (supportResponseLaw μ u) := by
    apply (hinfo.1.const_mul K).mono' hm.aestronglyMeasurable
    filter_upwards [hu] with y hy
    simpa only [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => hL0 i y))] using hy
  refine ⟨hi, ?_⟩
  have he := integral_mono_ae hi (hinfo.1.const_mul K) hu
  rwa [integral_const_mul, hinfo.2, mul_one] at he

end
end Nonsmooth
