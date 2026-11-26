import Nonsmooth.MaximumTailCost
import Nonsmooth.EventBarycenter
import Nonsmooth.ParametricEventKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def halfspacePosteriorKernel (ν : Measure E) [IsProbabilityMeasure ν] (u : E) : Kernel ℝ E :=
  parametricEventKernel ν {p : ℝ × E | ⟪p.2, u⟫_ℝ ≤ p.1}
    (measurableSet_le (continuous_snd.inner continuous_const).measurable measurable_fst)

instance halfspacePosteriorKernel_markov (ν : Measure E) [IsProbabilityMeasure ν] (u : E) :
    IsMarkovKernel (halfspacePosteriorKernel ν u) := by
  unfold halfspacePosteriorKernel
  infer_instance

def halfspacePosteriorShift (ν : Measure E) [IsProbabilityMeasure ν] (u : E) (y : ℝ) : E :=
  ∫ z, (z - ∫ a : E, a ∂ν) ∂halfspacePosteriorKernel ν u y

theorem halfspacePosteriorShift_measurable (ν : Measure E) [IsProbabilityMeasure ν] (u : E) :
    Measurable (halfspacePosteriorShift ν u) :=
  (stronglyMeasurable_id.sub stronglyMeasurable_const).integral_kernel.measurable

/-- The actual lower-halfspace posterior shift satisfies the event entropy
bound, using the centered MGF of the row law. -/
theorem halfspacePosteriorShift_entropy (ν : Measure E) [IsProbabilityMeasure ν] (u : E)
    (hi : Integrable (fun z : E => z) ν) {c : ℝ} (hc : 0 < c)
    (he : ∀ v : E, Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂ν⟫_ℝ) ν)
    (hb : ∀ v : E, (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂ν⟫_ℝ ∂ν) ≤ Real.exp (c * ‖v‖ ^ 2 / 2))
    (y : ℝ) (hy : 0 < cdf (ν.map (fun z : E => ⟪z, u⟫_ℝ)) y) :
    ‖halfspacePosteriorShift ν u y‖ ^ 2 ≤
      2 * c * Real.log (1 / cdf (ν.map (fun z : E => ⟪z, u⟫_ℝ)) y) := by
  have hu : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  letI : IsProbabilityMeasure (ν.map (fun z : E => ⟪z, u⟫_ℝ)) := Measure.isProbabilityMeasure_map hu.aemeasurable
  have hm : ν.real {z : E | ⟪z, u⟫_ℝ ≤ y} = cdf (ν.map (fun z : E => ⟪z, u⟫_ℝ)) y := by
    rw [cdf_eq_real, Measure.real, Measure.real, Measure.map_apply hu measurableSet_Iic]
    rfl
  have hA : ν {z : E | ⟪z, u⟫_ℝ ≤ y} ≠ 0 := by
    intro hz
    rw [← hm, Measure.real, hz, ENNReal.toReal_zero] at hy
    exact (lt_irrefl (0 : ℝ)) hy
  have h := event_barycenter_of_exp_moments (hi.sub (integrable_const _)) hc
    (by norm_num : (0 : ℝ) < 1) he (fun v => by simpa only [one_mul, Pi.sub_apply] using hb v)
    {z : E | ⟪z, u⟫_ℝ ≤ y} hA
  rw [hm] at h
  unfold halfspacePosteriorShift halfspacePosteriorKernel
  rw [parametricEventKernel_apply _ _ _ _ hA]
  exact h

theorem maximum_total_halfspace_shift [Nontrivial E] {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hi : ∀ i, Integrable (fun z : E => z) (μ i)) {c : ℝ} (hc : 0 < c)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2)) :
    Integrable (fun y => ∑ i, ‖halfspacePosteriorShift (μ i) u y‖ ^ 2) (supportResponseLaw μ u) ∧
      (∫ y, ∑ i, ‖halfspacePosteriorShift (μ i) u y‖ ^ 2 ∂supportResponseLaw μ u) ≤ 2 * c := by
  exact maximum_total_lower_tail_cost μ u hzero (fun i y => ‖halfspacePosteriorShift (μ i) u y‖ ^ 2)
    (fun i => ((halfspacePosteriorShift_measurable (μ i) u).norm).pow_const 2)
    (fun _ _ => sq_nonneg _) (fun i y hy => halfspacePosteriorShift_entropy (μ i) u (hi i) hc (he i) (hb i) y hy)

end
end Nonsmooth
