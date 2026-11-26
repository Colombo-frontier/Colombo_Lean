import Nonsmooth.GaussianCharacteristic
import Nonsmooth.GaussianTruncated
import Nonsmooth.GaussianAmbientRowLaw
import Nonsmooth.RotationalUniqueness

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussianLaw_nonzero : ∀ᵐ z : E ∂euclideanGaussianLaw E, z ≠ 0 := by
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  have hreal : ∀ᵐ z : ℝ ∂gaussianReal 0 1, z ≠ 0 :=
    (gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0)).ae_le
      (by
        convert! (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ) using 1 <;>
          simp only [Set.mem_singleton_iff])
  have hcoord := (euclideanGaussian_coordinate_measurePreserving (E := E) i).quasiMeasurePreserving.ae hreal
  filter_upwards [hcoord] with z hz
  intro he
  exact hz (by simp [he])

theorem truncatedGaussianLaw_nonzero : ∀ᵐ z : E ∂truncatedGaussianLaw E, z ≠ 0 :=
  Measure.ae_smul_measure (ae_restrict_of_ae (euclideanGaussianLaw_nonzero (E := E))) _

/-- Radial normalization of any nonzero rotation-invariant probability yields the
same actual spherical law used by the algorithm and posterior analysis. -/
theorem normalized_rotational_probability (μ : Measure E) [IsProbabilityMeasure μ]
    (hn : ∀ᵐ z ∂μ, z ≠ 0)
    (hi : ∀ e : E ≃ₗᵢ[ℝ] E, Measure.map e μ = μ) :
    Measure.map normalizedDirection μ = sphericalLaw E := by
  letI : IsProbabilityMeasure (Measure.map normalizedDirection μ) :=
    Measure.isProbabilityMeasure_map normalizedDirection_measurable.aemeasurable
  apply rotational_unit_probability_unique
  · apply (ae_map_iff normalizedDirection_measurable.aemeasurable
      (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
    exact hn.mono (fun z hz => normalizedDirection_norm hz)
  · intro e
    rw [Measure.map_map e.continuous.measurable normalizedDirection_measurable]
    have he : e ∘ normalizedDirection = normalizedDirection ∘ e :=
      funext (normalizedDirection_isometry e)
    rw [he, ← Measure.map_map normalizedDirection_measurable e.continuous.measurable, hi e]

theorem euclideanGaussianLaw_direction :
    Measure.map normalizedDirection (euclideanGaussianLaw E) = sphericalLaw E :=
  normalized_rotational_probability _ euclideanGaussianLaw_nonzero euclideanGaussianLaw_isometry

theorem truncatedGaussianLaw_direction :
    Measure.map normalizedDirection (truncatedGaussianLaw E) = sphericalLaw E :=
  normalized_rotational_probability _ truncatedGaussianLaw_nonzero truncatedGaussianLaw_isometry

theorem gaussianSupportRowLaw_direction :
    Measure.map (fun a : Feasible E 2 => normalizedDirection a.val) (gaussianSupportRowLaw E) =
      sphericalLaw E := by
  have hp : 0 < (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))
  have he (z : E) : normalizedDirection ((Real.sqrt (Module.finrank ℝ E))⁻¹ • z) = normalizedDirection z := by
    simp only [normalizedDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hp,
      mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  change Measure.map (normalizedDirection ∘ Subtype.val) (gaussianSupportRowLaw E) = _
  rw [← Measure.map_map normalizedDirection_measurable measurable_subtype_coe,
    gaussianSupportRowLaw_map, Measure.map_map normalizedDirection_measurable hm]
  simpa only [Function.comp_def, he] using truncatedGaussianLaw_direction (E := E)

end
end Nonsmooth
