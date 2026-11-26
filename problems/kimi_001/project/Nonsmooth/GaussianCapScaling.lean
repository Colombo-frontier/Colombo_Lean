import Nonsmooth.GaussianAxialCap
import Nonsmooth.GaussianHalfspaceMean

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianAmbientRow_halfspace_axial_variance {u : E} (hu : ‖u‖ = 1) (b : ℝ)
    (hpos : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    variance (fun z : E => ⟪z, u⟫_ℝ)
      ((gaussianAmbientRowLaw E)[|{z : E | ⟪z, u⟫_ℝ ≤ b}]) ≤ 1 / (Module.finrank ℝ E : ℝ) := by
  let c : ℝ := (Real.sqrt (Module.finrank ℝ E))⁻¹
  let f : E → E := fun z => c • z
  let C : Set E := {z : E | ⟪z, u⟫_ℝ ≤ b}
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hd)
  have hf : Measurable f := measurable_const.smul measurable_id
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hC : MeasurableSet C := measurableSet_le hr measurable_const
  have hrow : gaussianAmbientRowLaw E = (truncatedGaussianLaw E).map f := gaussianSupportRowLaw_map
  have hpre : f ⁻¹' C = {z : E | ⟪z, u⟫_ℝ ≤ b / c} := by
    ext z
    change ⟪c • z, u⟫_ℝ ≤ b ↔ ⟪z, u⟫_ℝ ≤ b / c
    rw [real_inner_smul_left, le_div_iff₀ hc, mul_comm]
  have hp : truncatedGaussianLaw E {z : E | ⟪z, u⟫_ℝ ≤ b / c} ≠ 0 := by
    change gaussianAmbientRowLaw E C ≠ 0 at hpos
    rwa [hrow, Measure.map_apply hf hC, hpre] at hpos
  change variance (fun z : E => ⟪z, u⟫_ℝ) ((gaussianAmbientRowLaw E)[|C]) ≤ _
  rw [hrow, conditioning_map_preimage _ f hf C hC, hpre,
    variance_map_measurable _ f hf _ hr]
  have he : ((fun z : E => ⟪z, u⟫_ℝ) ∘ f) = fun z : E => c * ⟪z, u⟫_ℝ := by
    funext z
    exact real_inner_smul_left _ _ _
  rw [he, variance_mul]
  have hbound := mul_le_mul_of_nonneg_left (truncatedGaussian_halfspace_axial_variance hu (b / c) hp)
    (sq_nonneg c)
  have hcsq : c ^ 2 = 1 / (Module.finrank ℝ E : ℝ) := by
    simp only [c, inv_pow, Real.sq_sqrt hd.le, one_div]
  simpa only [mul_one, hcsq] using hbound

theorem gaussianHalfspaceKernel_axial_variance {u : E} (hu : ‖u‖ = 1) (b : ℝ) :
    variance (fun z : E => ⟪z, u⟫_ℝ) (gaussianHalfspaceKernel u b) ≤
      1 / (Module.finrank ℝ E : ℝ) := by
  by_cases hpos : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} = 0
  · have he : gaussianHalfspaceKernel u b = gaussianAmbientRowLaw E := by
      change (if gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ b} = 0 then _ else _) = _
      rw [if_pos hpos]
    rw [he]
    have hi : AEStronglyMeasurable (fun z : E => ⟪z, u⟫_ℝ) (gaussianAmbientRowLaw E) :=
      (continuous_id.inner continuous_const).aestronglyMeasurable
    apply (variance_le_expectation_sq hi).trans
    simpa only [Pi.pow_apply, real_inner_comm u, hu, one_pow] using gaussianAmbientRow_inner_second_le u
  · rw [gaussianHalfspaceKernel, parametricEventKernel_apply _ _ _ _ hpos]
    exact gaussianAmbientRow_halfspace_axial_variance hu b hpos

end
end Nonsmooth
