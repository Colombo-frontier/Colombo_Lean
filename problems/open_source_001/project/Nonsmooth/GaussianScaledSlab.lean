import Nonsmooth.GaussianAxialSlab
import Nonsmooth.GaussianCapPerpendicular

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianAmbientRow_slab_axial_variance {u : E} (hu : ‖u‖ = 1) (a b : ℝ)
    (hpos : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    variance (fun z : E => ⟪z, u⟫_ℝ)
      ((gaussianAmbientRowLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}]) ≤ 1 / (Module.finrank ℝ E : ℝ) := by
  let c : ℝ := (Real.sqrt (Module.finrank ℝ E))⁻¹
  let f : E → E := fun z => c • z
  let C : Set E := {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hd)
  have hf : Measurable f := measurable_const.smul measurable_id
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hC : MeasurableSet C := (measurableSet_le measurable_const hr).inter (measurableSet_le hr measurable_const)
  have hrow : gaussianAmbientRowLaw E = (truncatedGaussianLaw E).map f := gaussianSupportRowLaw_map
  have hpre : f ⁻¹' C = {z : E | a / c ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b / c} := by
    ext z
    change (a ≤ ⟪c • z, u⟫_ℝ ∧ ⟪c • z, u⟫_ℝ ≤ b) ↔
      (a / c ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b / c)
    rw [real_inner_smul_left, div_le_iff₀ hc, le_div_iff₀ hc, mul_comm]
  have hp : truncatedGaussianLaw E {z : E | a / c ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b / c} ≠ 0 := by
    change gaussianAmbientRowLaw E C ≠ 0 at hpos
    rwa [hrow, Measure.map_apply hf hC, hpre] at hpos
  change variance (fun z : E => ⟪z, u⟫_ℝ) ((gaussianAmbientRowLaw E)[|C]) ≤ _
  rw [hrow, conditioning_map_preimage _ f hf C hC, hpre,
    variance_map_measurable _ f hf _ hr]
  have he : ((fun z : E => ⟪z, u⟫_ℝ) ∘ f) = fun z : E => c * ⟪z, u⟫_ℝ := by
    funext z
    exact real_inner_smul_left _ _ _
  rw [he, variance_mul]
  have hbound := mul_le_mul_of_nonneg_left (truncatedGaussian_slab_axial_variance hu (a / c) (b / c) hp)
    (sq_nonneg c)
  have hcsq : c ^ 2 = 1 / (Module.finrank ℝ E : ℝ) := by
    simp only [c, inv_pow, Real.sq_sqrt hd.le, one_div]
  simpa only [mul_one, hcsq] using hbound

theorem gaussianAmbientRow_slab_perpendicular_second {u w : E} (hu : ‖u‖ = 1)
    (hw : ⟪w, u⟫_ℝ = 0) (a b : ℝ)
    (hpos : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    (∫ z : E, ⟪w, z⟫_ℝ ^ 2 ∂(gaussianAmbientRowLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}]) ≤
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
  exact event_moment_le_of_slice_moments μ r hr hi _ hslice (Icc a b) measurableSet_Icc hpos

theorem gaussianAmbientRow_slab_isometry (u : E) (a b : ℝ) (e : E ≃ₗᵢ[ℝ] E) (hu : e u = u) :
    ((gaussianAmbientRowLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}]).map e =
      (gaussianAmbientRowLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}] := by
  let C : Set E := {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hC : MeasurableSet C :=
    (measurableSet_le measurable_const hr).inter (measurableSet_le hr measurable_const)
  have hpre : e ⁻¹' C = C := by
    ext z
    change (a ≤ ⟪e z, u⟫_ℝ ∧ ⟪e z, u⟫_ℝ ≤ b) ↔ (a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b)
    have hi : ⟪e z, u⟫_ℝ = ⟪z, u⟫_ℝ := by
      calc
        _ = ⟪e z, e u⟫_ℝ := by rw [hu]
        _ = _ := e.inner_map_map z u
    rw [hi]
  have h := conditioning_map_preimage (gaussianAmbientRowLaw E) e e.continuous.measurable C hC
  rw [gaussianAmbientRowLaw_isometry, hpre] at h
  exact h.symm

end
end Nonsmooth
