import Nonsmooth.GrunbaumApplication

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem functional_comp_equiv_ne_zero (L : E ≃L[ℝ] E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ℓ.comp L.toContinuousLinearMap ≠ 0 := by
  intro hz
  apply hℓ
  ext x
  have h := congrArg (fun q : E →L[ℝ] ℝ => q (L.symm x)) hz
  simpa using h

theorem linear_equiv_quarter_depth (L : E ≃L[ℝ] E) {K : Set E}
    (hdepth : ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume K ≤ volume (K ∩ {z | 0 ≤ ℓ z})) :
    ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 → ENNReal.ofReal (1 / 4 : ℝ) * volume (L '' K) ≤
      volume (L '' K ∩ {z | 0 ≤ ℓ z}) := by
  intro ℓ hℓ
  let q := ℓ.comp L.toContinuousLinearMap
  have h := hdepth q (functional_comp_equiv_ne_zero L ℓ hℓ)
  have heq : L '' K ∩ {z | 0 ≤ ℓ z} = L '' (K ∩ {z | 0 ≤ q z}) := by
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hle⟩
      exact ⟨x, ⟨hx, hle⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hle⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hle⟩
  rw [heq, addHaar_image_continuousLinearEquiv, addHaar_image_continuousLinearEquiv]
  simpa only [mul_left_comm] using
    mul_le_mul_left' h (ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)|)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_linear_equiv_volume_factor_pos (L : E ≃L[ℝ] E) :
    0 < ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| := by
  exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero)

theorem linear_equiv_volume_fraction_iff (L : E ≃L[ℝ] E) (K H : Set E) (κ : ℝ≥0∞) :
    volume (L '' H) + κ * volume (L '' K) ≤ volume (L '' K) ↔
      volume H + κ * volume K ≤ volume K := by
  rw [addHaar_image_continuousLinearEquiv, addHaar_image_continuousLinearEquiv]
  have hfactor := continuous_linear_equiv_volume_factor_pos L
  rw [mul_left_comm κ, ← mul_add]
  exact ENNReal.mul_le_mul_iff_right hfactor.ne' ENNReal.ofReal_ne_top

end
end Nonsmooth
