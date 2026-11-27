import Nonsmooth.AtomlessCDFEntropy
import Nonsmooth.GaussianProjectionAtoms
import Nonsmooth.FiniteProductKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {k : ℕ} [Nonempty (Fin k)]

def supportResponseLaw (μ : Fin k → Measure E) (u : E) : Measure ℝ :=
  (Measure.pi μ).map (fun a => finiteSupport a u)

theorem supportResponse_measurable (u : E) : Measurable (fun a : Fin k → E => finiteSupport a u) :=
  finiteSupport_joint_continuous.measurable.comp (measurable_id.prodMk measurable_const)

instance supportResponseLaw_probability (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    IsProbabilityMeasure (supportResponseLaw μ u) := Measure.isProbabilityMeasure_map (supportResponse_measurable u).aemeasurable

theorem supportResponseLaw_cdf (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) (y : ℝ) :
    cdf (supportResponseLaw μ u) y = ∏ i, cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y := by
  have hu : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  letI (i : Fin k) : IsProbabilityMeasure ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) :=
    Measure.isProbabilityMeasure_map hu.aemeasurable
  rw [cdf_eq_real, Measure.real, supportResponseLaw, Measure.map_apply (supportResponse_measurable u) measurableSet_Iic]
  change (Measure.pi μ {a | finiteSupport a u ≤ y}).toReal = _
  rw [independent_support_response_cdf, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [cdf_eq_real, Measure.real, Measure.map_apply hu measurableSet_Iic]
  rfl

theorem supportResponseLaw_atomless (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0) (y : ℝ) :
    supportResponseLaw μ u {y} = 0 := by
  have hcoord (i : Fin k) : Measure.pi μ {a : Fin k → E | ⟪a i, u⟫_ℝ = y} = 0 := by
    have he := finiteProductKernel_coordinate (fun i => Kernel.const Unit (μ i)) () i
    change (Measure.pi μ).map (fun a : Fin k → E => a i) = μ i at he
    have hu : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    have hz := hzero i y
    rw [← he, Measure.map_apply (measurable_pi_apply i) (measurableSet_eq_fun hu measurable_const)] at hz
    exact hz
  rw [supportResponseLaw, Measure.map_apply (supportResponse_measurable u) (measurableSet_singleton y)]
  apply measure_mono_null (t := ⋃ i : Fin k, {a : Fin k → E | ⟪a i, u⟫_ℝ = y})
  · intro a ha
    obtain ⟨i, hi⟩ := finiteSupport_attained a u
    exact mem_iUnion.mpr ⟨i, hi.symm.trans ha⟩
  · exact measure_iUnion_null_iff.mpr hcoord

theorem supportResponseLaw_cdf_positive_ae (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0) :
    ∀ᵐ y ∂supportResponseLaw μ u, ∀ i, 0 < cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y := by
  filter_upwards [atomless_cdf_interior_ae _ (supportResponseLaw_atomless μ u hzero)] with y hy
  have hp := hy.1
  rw [supportResponseLaw_cdf] at hp
  intro i
  have hn := (Finset.prod_ne_zero_iff.mp hp.ne') i (Finset.mem_univ i)
  exact lt_of_le_of_ne (cdf_nonneg _ _) (Ne.symm hn)

/-- The sum of all row lower-tail information costs at the observed maximum
has expectation exactly one, even when the independent row laws differ. -/
theorem supportResponseLaw_total_tail_information (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0) :
    Integrable (fun y => ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)) (supportResponseLaw μ u) ∧
      (∫ y, ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y) ∂supportResponseLaw μ u) = 1 := by
  have hi := atomless_cdf_log_inverse_moment _ (supportResponseLaw_atomless μ u hzero)
  have he : (fun y => Real.log (1 / cdf (supportResponseLaw μ u) y)) =ᵐ[supportResponseLaw μ u]
      (fun y => ∑ i, Real.log (1 / cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
    filter_upwards [supportResponseLaw_cdf_positive_ae μ u hzero] with y hy
    simp only [one_div, Real.log_inv]
    rw [supportResponseLaw_cdf, Real.log_prod (fun i _ => (hy i).ne')]
    exact (Finset.sum_neg_distrib _).symm
  exact ⟨hi.1.congr he, (integral_congr_ae he).symm.trans hi.2⟩

end
end Nonsmooth
