import Nonsmooth.RegularVectorMoments
import Nonsmooth.ScalarPairConcentration

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The vector's centered exponential moments follow from its regular plane
images. The constant four is uniform in the ambient dimension. -/
theorem regular_vector_centered_concentration (μ : Measure E) [IsProbabilityMeasure μ]
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ w : E, ‖w‖ = 1 → ⟪u, w⟫_ℝ = 0 → RegularProjectionImage μ u w) (v : E) :
    Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ⟫_ℝ) μ ∧
      (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ⟫_ℝ ∂μ) ≤ Real.exp (2 * ‖v‖ ^ 2) := by
  have hi := (regular_vector_memLp_two μ hu hd H).integrable (by norm_num)
  obtain ⟨w₀, hw₀, huw₀⟩ := exists_unit_orthogonal_direction hu hd
  let H₀ := H w₀ hw₀ huw₀
  have hmapu : μ.map (fun z : E => ⟪u, z⟫_ℝ) = realDensityLaw (potentialPartition H₀.potential) := by
    simpa only [real_inner_comm] using regular_projection_image_marginal μ u w₀ H₀
  let F : E → ℝ := fun z => ⟪u, z - ∫ a : E, a ∂μ⟫_ℝ
  have hF : Measurable F := (continuous_const.inner (continuous_id.sub continuous_const)).measurable
  have hFc (r : ℝ) : Integrable (fun z => Real.exp (r * F z)) μ ∧
      (∫ z, Real.exp (r * F z) ∂μ) ≤ Real.exp (r ^ 2 / 2) :=
    regular_marginal_inner_concentration μ hi u H₀.forward hmapu r
  rcases unit_axis_plane_decomposition hu v with ⟨a, hv⟩ | ⟨a, c, w, hw, huw, hv, hn⟩
  · have hf : (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ⟫_ℝ) =
        (fun z => Real.exp (a * F z)) := by
      funext z
      rw [hv, real_inner_smul_left]
    have hn : ‖v‖ ^ 2 = a ^ 2 := by simp [hv, norm_smul, Real.norm_eq_abs, hu, sq_abs]
    rw [hf]
    refine ⟨(hFc a).1, (hFc a).2.trans ?_⟩
    apply Real.exp_le_exp.mpr
    rw [hn]
    nlinarith [sq_nonneg a]
  · let Hw := H w hw huw
    let G : E → ℝ := fun z => ⟪w, z - ∫ a : E, a ∂μ⟫_ℝ
    have hG : Measurable G := (continuous_const.inner (continuous_id.sub continuous_const)).measurable
    have hGc (r : ℝ) : Integrable (fun z => Real.exp (r * G z)) μ ∧
        (∫ z, Real.exp (r * G z) ∂μ) ≤ Real.exp (r ^ 2 / 2) :=
      regular_marginal_inner_concentration μ hi w Hw.backward
        (regular_projection_image_second_marginal μ u w Hw) r
    have hf : (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ⟫_ℝ) =
        (fun z => Real.exp (a * F z + c * G z)) := by
      funext z
      rw [hv, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [hf]
    simpa only [hn] using scalar_pair_unit_mgf μ F G hF hG hFc hGc a c

end
end Nonsmooth
