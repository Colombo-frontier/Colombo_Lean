import Nonsmooth.GaussianNegativeCap

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem variance_le_centered_second {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hi : Integrable f μ) (c : ℝ) :
    variance f μ ≤ ∫ x, (f x - c) ^ 2 ∂μ := by
  have hm := hi.aestronglyMeasurable.aemeasurable
  have he : variance (fun x => f x - c) μ = variance f μ := by
    rw [variance_eq_integral (hm.sub_const c), variance_eq_integral hm,
      integral_sub hi (integrable_const c), integral_const]
    simp only [probReal_univ, one_smul]
    congr 1
    funext x
    ring
  rw [← he]
  exact variance_le_expectation_sq (hi.aestronglyMeasurable.sub aestronglyMeasurable_const)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem truncatedGaussian_unit_scalar_second {u : E} (hu : ‖u‖ = 1) :
    (∫ z : E, ⟪z, u⟫_ℝ ^ 2 ∂truncatedGaussianLaw E) ≤ 1 := by
  have hV : MemLp (fun z : E => z) 2 (truncatedGaussianLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable _ truncatedGaussianLaw_supported
  have he := rotational_second_moment (truncatedGaussianLaw E) truncatedGaussianLaw_isometry hV u
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  simp only [hu, one_pow, one_mul] at he
  simp only [real_inner_comm u]
  rw [he, div_le_one hd]
  exact truncatedGaussian_norm_second_le

theorem truncatedGaussian_scalar_law_symmetric (u : E) :
    ((truncatedGaussianLaw E).map (fun z : E => ⟪z, u⟫_ℝ)).map (fun x : ℝ => -x) =
      (truncatedGaussianLaw E).map (fun z : E => ⟪z, u⟫_ℝ) := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  rw [Measure.map_map measurable_neg hr]
  have he : (fun x : ℝ => -x) ∘ (fun z : E => ⟪z, u⟫_ℝ) =
      (fun z : E => ⟪z, u⟫_ℝ) ∘ e := by
    funext z
    change -⟪z, u⟫_ℝ = ⟪-z, u⟫_ℝ
    rw [inner_neg_left]
  rw [he, ← Measure.map_map hr e.continuous.measurable, truncatedGaussianLaw_isometry]

theorem truncatedGaussian_negative_halfspace_second {u : E} (hu : ‖u‖ = 1)
    {b : ℝ} (hb : b ≤ 0) (hpos : truncatedGaussianLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    (∫ z : E, (⟪z, u⟫_ℝ - b) ^ 2 ∂(truncatedGaussianLaw E)[|{z : E | ⟪z, u⟫_ℝ ≤ b}]) ≤ 1 := by
  let R : ℝ := 2 * Real.sqrt (Module.finrank ℝ E)
  let B : Set E := closedBall (0 : E) R
  let C : Set E := {z : E | ⟪z, u⟫_ℝ ≤ b}
  have hC : MeasurableSet C := measurableSet_le
    (show Measurable (fun z : E => ⟪z, u⟫_ℝ) from (continuous_id.inner continuous_const).measurable)
    measurable_const
  have hB : MeasurableSet B := measurableSet_closedBall
  have hR : 0 ≤ R := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hgeom : B ∩ C = {z : E | ‖z‖ ^ 2 ≤ R ^ 2 ∧ ⟪z, u⟫_ℝ ≤ b} := by
    ext z
    change (z ∈ closedBall (0 : E) R ∧ ⟪z, u⟫_ℝ ≤ b) ↔ _
    simp only [mem_closedBall, dist_zero_right, mem_setOf_eq, sq_le_sq₀ (norm_nonneg z) hR]
  have hrawpos : euclideanGaussianLaw E (B ∩ C) ≠ 0 := by
    intro hz
    apply hpos
    change (euclideanGaussianLaw E)[|B] C = 0
    rw [cond_apply hB, hz, mul_zero]
  have hp : 0 < (euclideanGaussianLaw E).real (B ∩ C) :=
    ENNReal.toReal_pos hrawpos (measure_ne_top _ _)
  change (∫ z : E, (⟪z, u⟫_ℝ - b) ^ 2 ∂(euclideanGaussianLaw E)[|B][|C]) ≤ 1
  rw [cond_cond_eq_cond_inter hB hC, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul]
  change ((euclideanGaussianLaw E).real (B ∩ C))⁻¹ *
    (∫ z in B ∩ C, (⟪z, u⟫_ℝ - b) ^ 2 ∂euclideanGaussianLaw E) ≤ 1
  rw [← div_eq_inv_mul, div_le_one hp, hgeom]
  exact euclideanGaussian_negative_cap_second hu R hb

theorem truncatedGaussian_halfspace_axial_variance {u : E} (hu : ‖u‖ = 1) (b : ℝ)
    (hpos : truncatedGaussianLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    variance (fun z : E => ⟪z, u⟫_ℝ)
      ((truncatedGaussianLaw E)[|{z : E | ⟪z, u⟫_ℝ ≤ b}]) ≤ 1 := by
  let μ := truncatedGaussianLaw E
  let r : E → ℝ := fun z => ⟪z, u⟫_ℝ
  have hr : Measurable r := (continuous_id.inner continuous_const).measurable
  have hV : MemLp (fun z : E => z) 2 μ :=
    MemLp.of_bound measurable_id.aestronglyMeasurable _ truncatedGaussianLaw_supported
  have hLp : MemLp r 2 μ := by simpa only [r, real_inner_comm u] using hV.const_inner u
  letI := cond_isProbabilityMeasure hpos
  by_cases hb : b ≤ 0
  · apply (variance_le_centered_second _
      (integrable_under_event (hLp.integrable (by norm_num)) hpos) b).trans
    exact truncatedGaussian_negative_halfspace_second hu hb hpos
  · let ν := μ.map r
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
    have hνLp : MemLp (fun x : ℝ => x) 2 ν :=
      (memLp_map_measure_iff measurable_id.aestronglyMeasurable hr.aemeasurable).mpr hLp
    have he := symmetric_nonnegative_halfspace_second ν
      (truncatedGaussian_scalar_law_symmetric u) hνLp.integrable_sq (le_of_lt (lt_of_not_ge hb))
    have hsq : StronglyMeasurable (fun x : ℝ => x ^ 2) := (continuous_id.pow 2).stronglyMeasurable
    have hmap : ν[|Iic b] = (μ[|{z : E | ⟪z, u⟫_ℝ ≤ b}]).map r :=
      conditioning_map_preimage μ r hr _ measurableSet_Iic
    rw [hmap, integral_map_of_stronglyMeasurable hr hsq,
      integral_map_of_stronglyMeasurable hr hsq] at he
    have hi := variance_le_expectation_sq
      (μ := μ[|{z : E | ⟪z, u⟫_ℝ ≤ b}]) hr.aestronglyMeasurable
    exact hi.trans (he.trans (truncatedGaussian_unit_scalar_second hu))

end
end Nonsmooth
