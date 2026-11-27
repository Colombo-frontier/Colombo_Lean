import Nonsmooth.GaussianPolar
import Nonsmooth.GaussianAmbientRowLaw

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianAmbientRowLaw_nonzero : ∀ᵐ z : E ∂gaussianAmbientRowLaw E, z ≠ 0 := by
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map]
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  apply (ae_map_iff hm.aemeasurable (measurableSet_singleton (0 : E)).compl).mpr
  filter_upwards [truncatedGaussianLaw_nonzero (E := E)] with z hz
  exact smul_ne_zero (inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)).ne') hz

theorem gaussianAmbientRowLaw_polar :
    Measure.map (fun z : E => (‖z‖, normalizedDirection z)) (gaussianAmbientRowLaw E) =
      (Measure.map (fun z : E => ‖z‖) (gaussianAmbientRowLaw E)).prod (sphericalLaw E) :=
  rotational_radius_direction_product _ gaussianAmbientRowLaw_nonzero gaussianAmbientRowLaw_isometry

theorem gaussianAmbientRowLaw_radial_reconstruct :
    Measure.map (fun p : ℝ × E => p.1 • p.2)
      ((Measure.map (fun z : E => ‖z‖) (gaussianAmbientRowLaw E)).prod (sphericalLaw E)) =
        gaussianAmbientRowLaw E := by
  rw [← gaussianAmbientRowLaw_polar, Measure.map_map (g := fun p : ℝ × E => p.1 • p.2) (measurable_fst.smul measurable_snd)
    (continuous_norm.measurable.prodMk normalizedDirection_measurable)]
  have hid : ((fun p : ℝ × E => p.1 • p.2) ∘
      (fun z : E => (‖z‖, normalizedDirection z))) = id :=
    funext normalizedDirection_reconstruct
  rw [hid]
  exact Measure.map_id

theorem gaussianAmbientRowLaw_norm_large (hd : 86 ≤ Module.finrank ℝ E) :
    7 / 8 ≤ (gaussianAmbientRowLaw E).real {z : E | 1 / 2 ≤ ‖z‖} := by
  rw [gaussianAmbientRowLaw, map_measureReal_apply measurable_subtype_coe
    (isClosed_le continuous_const continuous_norm).measurableSet]
  exact gaussianSupportRowLaw_norm_large hd

theorem gaussianSupportRowLaw_polar :
    Measure.map (fun z : Feasible E 2 => (‖z.val‖, normalizedDirection z.val)) (gaussianSupportRowLaw E) =
      (Measure.map (fun z : E => ‖z‖) (gaussianAmbientRowLaw E)).prod (sphericalLaw E) := by
  rw [← gaussianAmbientRowLaw_polar, gaussianAmbientRowLaw,
    Measure.map_map (continuous_norm.measurable.prodMk normalizedDirection_measurable) measurable_subtype_coe]
  rfl

end
end Nonsmooth
