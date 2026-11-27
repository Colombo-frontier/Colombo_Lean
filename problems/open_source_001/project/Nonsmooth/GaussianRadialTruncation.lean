import Nonsmooth.GaussianEventSlices
import Nonsmooth.RotationalCovariance
import Nonsmooth.TruncationMonotonicity

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussian_radial_threshold_isometry (t : ℝ) (e : E ≃ₗᵢ[ℝ] E) :
    ((euclideanGaussianLaw E)[|{z : E | ‖z‖ ^ 2 ≤ t}]).map e =
      (euclideanGaussianLaw E)[|{z : E | ‖z‖ ^ 2 ≤ t}] := by
  have hA : MeasurableSet {z : E | ‖z‖ ^ 2 ≤ t} :=
    measurableSet_le (continuous_norm.pow 2).measurable measurable_const
  have hp : e ⁻¹' {z : E | ‖z‖ ^ 2 ≤ t} = {z : E | ‖z‖ ^ 2 ≤ t} := by
    ext z
    simp only [mem_preimage, mem_setOf_eq, e.norm_map]
  have he := conditioning_map_preimage (euclideanGaussianLaw E) e e.continuous.measurable _ hA
  rw [euclideanGaussianLaw_isometry, hp] at he
  exact he.symm

theorem gaussian_radial_threshold_memLp (t : ℝ)
    (hpos : euclideanGaussianLaw E {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) :
    MemLp (fun z : E => z) 2 (euclideanGaussianLaw E)[|{z : E | ‖z‖ ^ 2 ≤ t}] :=
  (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
    (integrable_under_event euclideanGaussian_norm_square_integrable hpos)

theorem gaussian_radial_threshold_norm_second (t : ℝ)
    (hpos : euclideanGaussianLaw E {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) :
    (∫ z : E, ‖z‖ ^ 2 ∂(euclideanGaussianLaw E)[|{z : E | ‖z‖ ^ 2 ≤ t}]) ≤
      (Module.finrank ℝ E : ℝ) := by
  have hA : MeasurableSet {z : E | ‖z‖ ^ 2 ≤ t} :=
    measurableSet_le (continuous_norm.pow 2).measurable measurable_const
  rw [← euclideanGaussian_norm_second_moment (E := E)]
  apply integral_event_le_of_separated euclideanGaussian_norm_square_integrable hA hpos t
  · exact (ae_restrict_mem hA).mono (fun _ hz => hz)
  · exact (ae_restrict_mem hA.compl).mono
      (fun z hz => (lt_of_not_ge (show ¬ ‖z‖ ^ 2 ≤ t from hz)).le)

theorem gaussian_radial_threshold_directional_second (t : ℝ)
    (hpos : euclideanGaussianLaw E {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) (u : E) :
    (∫ z : E, ⟪u, z⟫_ℝ ^ 2 ∂(euclideanGaussianLaw E)[|{z : E | ‖z‖ ^ 2 ≤ t}]) ≤ ‖u‖ ^ 2 := by
  rw [rotational_second_moment _ (gaussian_radial_threshold_isometry t)
    (gaussian_radial_threshold_memLp t hpos)]
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  apply (div_le_iff₀ hd).mpr
  exact mul_le_mul_of_nonneg_left (gaussian_radial_threshold_norm_second t hpos) (sq_nonneg ‖u‖)

theorem gaussian_radial_threshold_mean_zero (t : ℝ) :
    (∫ z : E, z ∂(euclideanGaussianLaw E)[|{z : E | ‖z‖ ^ 2 ≤ t}]) = 0 := by
  let μ := (euclideanGaussianLaw E)[|{z : E | ‖z‖ ^ 2 ≤ t}]
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hp : MeasurePreserving e μ μ := ⟨e.continuous.measurable, gaussian_radial_threshold_isometry t e⟩
  have he := hp.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun z : E => z)
  change (∫ z : E, -z ∂μ) = ∫ z : E, z ∂μ at he
  rw [integral_neg] at he
  have hz : (2 : ℝ) • (∫ z : E, z ∂μ) = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp he
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end
end Nonsmooth
