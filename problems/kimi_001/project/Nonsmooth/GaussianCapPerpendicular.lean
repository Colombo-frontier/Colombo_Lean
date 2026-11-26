import Nonsmooth.ConditionalEventMoments
import Nonsmooth.GaussianCapScaling

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianAmbientRow_halfspace_perpendicular_second {u w : E} (hu : ‖u‖ = 1)
    (hw : ⟪w, u⟫_ℝ = 0) (b : ℝ)
    (hpos : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    (∫ z : E, ⟪w, z⟫_ℝ ^ 2 ∂(gaussianAmbientRowLaw E)[|{z : E | ⟪z, u⟫_ℝ ≤ b}]) ≤
      ‖w‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  let μ := gaussianAmbientRowLaw E
  let r : E → ℝ := fun z => ⟪z, u⟫_ℝ
  have hr : Measurable r := (continuous_id.inner continuous_const).measurable
  have hi : Integrable (fun z : E => ⟪w, z⟫_ℝ ^ 2) μ :=
    (gaussianAmbientRowLaw_memLp.const_inner w).integrable_sq
  have hbound := condDistrib_ae_support μ r hr id measurable_id
    (B := {z : E | ‖z‖ ≤ 2}) (measurableSet_le continuous_norm.measurable measurable_const)
    gaussianAmbientRowLaw_norm_le_two
  have hslice : ∀ᵐ y ∂μ.map r, (∫ z : E, ⟪w, z⟫_ℝ ^ 2 ∂condDistrib id r μ y) ≤
      ‖w‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
    filter_upwards [hbound, gaussianAmbientRowLaw_projection_slice_mean hu,
      gaussianAmbientRow_scalar_covariance hu] with y hb hm hc
    have hV : MemLp (fun z : E => z) 2 (condDistrib id r μ y) :=
      MemLp.of_bound measurable_id.aestronglyMeasurable 2 hb
    have hmean : (∫ z : E, ⟪w, z⟫_ℝ ∂condDistrib id r μ y) = 0 := by
      rw [integral_inner (hV.integrable (by norm_num)), hm, real_inner_smul_right, hw, mul_zero]
    have he := hc w
    rw [variance_of_integral_eq_zero (hV.const_inner w).aestronglyMeasurable.aemeasurable hmean] at he
    exact he
  exact event_moment_le_of_slice_moments μ r hr hi _ hslice (Iic b) measurableSet_Iic hpos

theorem gaussianHalfspaceKernel_perpendicular_second {u w : E} (hu : ‖u‖ = 1)
    (hw : ⟪w, u⟫_ℝ = 0) (b : ℝ) :
    (∫ z : E, ⟪w, z⟫_ℝ ^ 2 ∂gaussianHalfspaceKernel u b) ≤
      ‖w‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  by_cases hpos : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} = 0
  · have he : gaussianHalfspaceKernel u b = gaussianAmbientRowLaw E := by
      change (if gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} = 0 then _ else _) = _
      rw [if_pos hpos]
    rw [he]
    exact gaussianAmbientRow_inner_second_le w
  · rw [gaussianHalfspaceKernel, parametricEventKernel_apply _ _ _ _ hpos]
    exact gaussianAmbientRow_halfspace_perpendicular_second hu hw b hpos

end
end Nonsmooth
