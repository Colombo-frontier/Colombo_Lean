import Nonsmooth.GaussianNegativeSlab
import Nonsmooth.GaussianAxialCap

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem truncatedGaussian_negative_slab_second {u : E} (hu : ‖u‖ = 1)
    (a : ℝ) {b : ℝ} (hb : b ≤ 0) (hpos : truncatedGaussianLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    (∫ z : E, (⟪z, u⟫_ℝ - b) ^ 2 ∂(truncatedGaussianLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}]) ≤ 1 := by
  let R : ℝ := 2 * Real.sqrt (Module.finrank ℝ E)
  let B : Set E := closedBall (0 : E) R
  let C : Set E := {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}
  have hproj : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hC : MeasurableSet C :=
    (measurableSet_le measurable_const hproj).inter (measurableSet_le hproj measurable_const)
  have hB : MeasurableSet B := measurableSet_closedBall
  have hR : 0 ≤ R := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hgeom : B ∩ C = {z : E | ‖z‖ ^ 2 ≤ R ^ 2 ∧ a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} := by
    ext z
    change (z ∈ closedBall (0 : E) R ∧ a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b) ↔ _
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
  exact euclideanGaussian_negative_slab_second hu R a hb

theorem truncatedGaussian_slab_axial_variance {u : E} (hu : ‖u‖ = 1) (a b : ℝ)
    (hpos : truncatedGaussianLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    variance (fun z : E => ⟪z, u⟫_ℝ)
      ((truncatedGaussianLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}]) ≤ 1 := by
  let μ := truncatedGaussianLaw E
  let r : E → ℝ := fun z => ⟪z, u⟫_ℝ
  let A : Set E := {z : E | a ≤ r z ∧ r z ≤ b}
  have hr : Measurable r := (continuous_id.inner continuous_const).measurable
  have hV : MemLp (fun z : E => z) 2 μ :=
    MemLp.of_bound measurable_id.aestronglyMeasurable _ truncatedGaussianLaw_supported
  have hLp : MemLp r 2 μ := by simpa only [r, real_inner_comm u] using hV.const_inner u
  letI := cond_isProbabilityMeasure hpos
  by_cases hb : b ≤ 0
  · apply (variance_le_centered_second _
      (integrable_under_event (hLp.integrable (by norm_num)) hpos) b).trans
    exact truncatedGaussian_negative_slab_second hu a hb hpos
  by_cases ha : 0 ≤ a
  · have hu' : ‖-u‖ = 1 := by simpa only [norm_neg] using hu
    have he : {z : E | -b ≤ ⟪z, -u⟫_ℝ ∧ ⟪z, -u⟫_ℝ ≤ -a} = A := by
      ext z
      simp only [mem_setOf_eq, inner_neg_right, A, r]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have hp' : truncatedGaussianLaw E {z : E | -b ≤ ⟪z, -u⟫_ℝ ∧ ⟪z, -u⟫_ℝ ≤ -a} ≠ 0 := by
      rw [he]
      exact hpos
    have hsecond := truncatedGaussian_negative_slab_second hu' (-b) (neg_nonpos.mpr ha) hp'
    rw [he] at hsecond
    have hfun : (fun z : E => (⟪z, -u⟫_ℝ - -a) ^ 2) = fun z : E => (r z - a) ^ 2 := by
      funext z
      simp only [inner_neg_right, r]
      ring
    rw [hfun] at hsecond
    exact (variance_le_centered_second _
      (integrable_under_event (hLp.integrable (by norm_num)) hpos) a).trans hsecond
  · let ν := μ.map r
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
    have hνLp : MemLp (fun x : ℝ => x) 2 ν :=
      (memLp_map_measure_iff measurable_id.aestronglyMeasurable hr.aemeasurable).mpr hLp
    have he := symmetric_straddling_interval_second ν
      (truncatedGaussian_scalar_law_symmetric u) hνLp.integrable_sq
      (le_of_lt (lt_of_not_ge ha)) (le_of_lt (lt_of_not_ge hb))
    have hsq : StronglyMeasurable (fun x : ℝ => x ^ 2) := (continuous_id.pow 2).stronglyMeasurable
    have hmap : ν[|Icc a b] = (μ[|A]).map r :=
      conditioning_map_preimage μ r hr _ measurableSet_Icc
    rw [hmap, integral_map_of_stronglyMeasurable hr hsq,
      integral_map_of_stronglyMeasurable hr hsq] at he
    have hi := variance_le_expectation_sq (μ := μ[|A]) hr.aestronglyMeasurable
    exact hi.trans (he.trans (truncatedGaussian_unit_scalar_second hu))

end
end Nonsmooth
