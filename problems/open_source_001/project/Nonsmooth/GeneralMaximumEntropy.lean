import Nonsmooth.GeneralCDFEntropy
import Nonsmooth.SupportMaximumEntropy

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)]

theorem supportResponseLaw_cdf_positive_ae_general (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    ∀ᵐ y ∂supportResponseLaw μ u, ∀ i,
      0 < cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y := by
  filter_upwards [cdf_positive_ae (supportResponseLaw μ u)] with y hy
  rw [supportResponseLaw_cdf] at hy
  intro i
  have hn := (Finset.prod_ne_zero_iff.mp hy.ne') i (Finset.mem_univ i)
  exact lt_of_le_of_ne (cdf_nonneg _ _) (Ne.symm hn)

/-- The sum of all lower-tail information costs at the observed maximum has
expectation at most one, allowing arbitrary atoms in each row observation. -/
theorem supportResponseLaw_total_tail_information_le (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    Integrable (fun y => ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y))
      (supportResponseLaw μ u) ∧
      (∫ y, ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)
        ∂supportResponseLaw μ u) ≤ 1 := by
  have hi := cdf_log_inverse_moment_le_one (supportResponseLaw μ u)
  have he : (fun y => Real.log (1 / cdf (supportResponseLaw μ u) y)) =ᵐ[supportResponseLaw μ u]
      (fun y => ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
    filter_upwards [supportResponseLaw_cdf_positive_ae_general μ u] with y hy
    simp only [one_div, Real.log_inv]
    rw [supportResponseLaw_cdf, Real.log_prod (fun i _ => (hy i).ne')]
    exact (Finset.sum_neg_distrib _).symm
  exact ⟨hi.1.congr he, (integral_congr_ae he).symm.trans_le hi.2⟩

end
end Nonsmooth
