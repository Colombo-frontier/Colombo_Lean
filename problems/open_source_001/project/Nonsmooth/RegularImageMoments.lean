import Nonsmooth.RegularVectorNoSpike

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem regular_marginal_image_memLp {α : Type} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (hX : Measurable X)
    {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V)
    (hlaw : μ.map X = realDensityLaw (potentialPartition V)) : MemLp X 2 μ := by
  have h := (regularFamily_marginal_probability_and_memLp H).2
  rw [← hlaw] at h
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hX.aemeasurable).mp h

theorem regular_marginal_image_concentration {α : Type} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (hX : Measurable X)
    {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V)
    (hlaw : μ.map X = realDensityLaw (potentialPartition V)) (r : ℝ) :
    Integrable (fun x => Real.exp (r * (X x - ∫ a, X a ∂μ))) μ ∧
      (∫ x, Real.exp (r * (X x - ∫ a, X a ∂μ)) ∂μ) ≤ Real.exp (r ^ 2 / 2) := by
  have hm : (∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) = ∫ a, X a ∂μ := by
    rw [← hlaw]
    exact integral_map_of_stronglyMeasurable hX stronglyMeasurable_id
  have hi := regularFamily_marginal_centered_exp_integrable H r
  have hb := regularFamily_marginal_centered_mgf H r
  rw [hm, ← hlaw] at hi hb
  have hf : Measurable (fun y : ℝ => Real.exp (r * (y - ∫ a, X a ∂μ))) := by fun_prop
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).mp hi, ?_⟩
  rwa [integral_map_of_stronglyMeasurable hX hf.stronglyMeasurable] at hb

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem regular_projection_image_second_marginal (μ : Measure E) (u v : E)
    (H : RegularProjectionImage μ u v) :
    μ.map (fun z : E => ⟪v, z⟫_ℝ) = realDensityLaw (potentialPartition (fun t x => H.potential x t)) := by
  have hX : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hY : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  rw [← potentialJointLaw_second_marginal H.potential H.forward.measurable
    (regularFamily_slice_integrable H.backward), ← H.law,
    Measure.map_map measurable_snd (hX.prodMk hY)]
  rfl

theorem regular_projection_image_coordinate_moments (μ : Measure E) (u v : E)
    (H : RegularProjectionImage μ u v) :
    MemLp (fun z : E => ⟪u, z⟫_ℝ) 2 μ ∧ MemLp (fun z : E => ⟪v, z⟫_ℝ) 2 μ := by
  have hX : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hY : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  have hx := regular_marginal_image_memLp μ _ hX H.forward (regular_projection_image_marginal μ u v H)
  have hy := regular_marginal_image_memLp μ _ hY H.backward (regular_projection_image_second_marginal μ u v H)
  refine ⟨?_, hy⟩
  convert hx using 1
  funext z
  exact real_inner_comm _ _

theorem regular_marginal_inner_concentration (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (v : E)
    {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V)
    (hlaw : μ.map (fun z : E => ⟪v, z⟫_ℝ) = realDensityLaw (potentialPartition V)) (r : ℝ) :
    Integrable (fun z => Real.exp (r * ⟪v, z - ∫ a : E, a ∂μ⟫_ℝ)) μ ∧
      (∫ z, Real.exp (r * ⟪v, z - ∫ a : E, a ∂μ⟫_ℝ) ∂μ) ≤ Real.exp (r ^ 2 / 2) := by
  have hY : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  have h := regular_marginal_image_concentration μ _ hY H hlaw r
  simpa only [integral_inner hi, inner_sub_right] using h

end
end Nonsmooth
