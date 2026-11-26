import NCConcave16991.MixedHaarGaussianReservoir
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # The actual normalized standard Gaussian and its rotational invariance -/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def normalize (g : E) : E := ‖g‖⁻¹ • g

theorem normalize_measurable : Measurable (normalize (E := E)) := measurable_id.norm.inv.smul measurable_id

theorem normalize_norm {g : E} (hg : g ≠ 0) : ‖normalize g‖ = 1 := by
  rw [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg g),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)]

theorem normalize_isometry (U : E ≃ₗᵢ[ℝ] E) (g : E) : normalize (U g) = U (normalize g) := by
  simp only [normalize, U.norm_map, map_smul]

def normalizedGaussianLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] : Measure E := (stdGaussian E).map normalize

instance normalizedGaussianLaw_probability : IsProbabilityMeasure (normalizedGaussianLaw E) := by
  unfold normalizedGaussianLaw
  infer_instance

theorem stdGaussian_ne_dirac_of_unit (e : E) (he : ‖e‖ = 1) (x : E) : stdGaussian E ≠ Measure.dirac x := by
  intro hx
  have hh := variance_dual_stdGaussian (innerSL ℝ e)
  rw [hx, variance_dirac, innerSL_apply_norm, he] at hh
  norm_num at hh

theorem stdGaussian_ne_zero_ae (e : E) (he : ‖e‖ = 1) : ∀ᵐ g ∂stdGaussian E, g ≠ 0 := by
  letI : NullSingletonClass (stdGaussian E) :=
    IsGaussian.nullSingletonClass (stdGaussian_ne_dirac_of_unit e he)
  rw [ae_iff]
  simpa only [not_not, Set.setOf_eq_eq_singleton] using measure_singleton (0 : E)

theorem normalizedGaussianLaw_unit (e : E) (he : ‖e‖ = 1) :
    ∀ᵐ x ∂normalizedGaussianLaw E, ‖x‖ = 1 := by
  unfold normalizedGaussianLaw
  apply (ae_map_iff normalize_measurable.aemeasurable
    (p := fun x : E ↦ ‖x‖ = 1)
    (measurableSet_eq_fun (measurable_id.norm : Measurable (fun x : E ↦ ‖x‖)) measurable_const)).mpr
  filter_upwards [stdGaussian_ne_zero_ae e he] with g hg
  exact normalize_norm hg

theorem normalizedGaussianLaw_rotation (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving U (normalizedGaussianLaw E) (normalizedGaussianLaw E) := by
  refine ⟨U.continuous.measurable, ?_⟩
  unfold normalizedGaussianLaw
  rw [Measure.map_map U.continuous.measurable normalize_measurable]
  change (stdGaussian E).map (fun x : E ↦ U (normalize x)) = (stdGaussian E).map normalize
  have he : (fun x : E ↦ U (normalize x)) = (fun x : E ↦ normalize (U x)) := by
    funext x
    exact (normalize_isometry U x).symm
  rw [he]
  change (stdGaussian E).map (normalize ∘ U) = (stdGaussian E).map normalize
  rw [← Measure.map_map normalize_measurable U.continuous.measurable, stdGaussian_map]

end NCConcave16991.MixedHaar
