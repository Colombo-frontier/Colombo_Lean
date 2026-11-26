import Nonsmooth.GeneralMaximumEntropy
import Nonsmooth.HalfspacePosteriorShift

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)]

theorem maximum_total_lower_tail_cost_general (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (L : Fin k → ℝ → ℝ) (hL : ∀ i, Measurable (L i))
    (hL0 : ∀ i y, 0 ≤ L i y) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ i y, 0 < cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y →
      L i y ≤ K * Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)) :
    Integrable (fun y => ∑ i, L i y) (supportResponseLaw μ u) ∧
      (∫ y, ∑ i, L i y ∂supportResponseLaw μ u) ≤ K := by
  have hinfo := supportResponseLaw_total_tail_information_le μ u
  have hu : (fun y => ∑ i, L i y) ≤ᵐ[supportResponseLaw μ u]
      (fun y => K * ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
    filter_upwards [supportResponseLaw_cdf_positive_ae_general μ u] with y hy
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hb i y (hy i))
  have hm : Measurable (fun y => ∑ i, L i y) := by fun_prop
  have hi : Integrable (fun y => ∑ i, L i y) (supportResponseLaw μ u) := by
    apply (hinfo.1.const_mul K).mono' hm.aestronglyMeasurable
    filter_upwards [hu] with y hy
    simpa only [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => hL0 i y))] using hy
  refine ⟨hi, ?_⟩
  have he := integral_mono_ae hi (hinfo.1.const_mul K) hu
  rw [integral_const_mul] at he
  exact he.trans ((mul_le_mul_of_nonneg_left hinfo.2 hK).trans_eq (mul_one K))

theorem maximum_total_halfspace_shift_general (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hi : ∀ i, Integrable (fun z : E => z) (μ i)) {c : ℝ} (hc : 0 < c)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤
      Real.exp (c * ‖v‖ ^ 2 / 2)) :
    Integrable (fun y => ∑ i, ‖halfspacePosteriorShift (μ i) u y‖ ^ 2) (supportResponseLaw μ u) ∧
      (∫ y, ∑ i, ‖halfspacePosteriorShift (μ i) u y‖ ^ 2 ∂supportResponseLaw μ u) ≤ 2 * c := by
  exact maximum_total_lower_tail_cost_general μ u
    (fun i y => ‖halfspacePosteriorShift (μ i) u y‖ ^ 2)
    (fun i => ((halfspacePosteriorShift_measurable (μ i) u).norm).pow_const 2)
    (fun _ _ => sq_nonneg _) (by positivity)
    (fun i y hy => halfspacePosteriorShift_entropy (μ i) u (hi i) hc (he i) (hb i) y hy)

end
end Nonsmooth
