import Nonsmooth.CenteredBodyTranslation
import Nonsmooth.LinearDepthTransport

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def bodyPullback (c : E) (L : E ≃L[ℝ] E) : E ≃ₜ E :=
  L.symm.toHomeomorph.trans (Homeomorph.addLeft c)

def bodyPullbackAffine (c : E) (L : E ≃L[ℝ] E) : E →ᵃ[ℝ] E :=
  (AffineEquiv.constVAdd ℝ E c).toAffineMap.comp L.symm.toLinearEquiv.toAffineEquiv.toAffineMap

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem bodyPullback_apply (c : E) (L : E ≃L[ℝ] E) (z : E) :
    bodyPullback c L z = c + L.symm z := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem bodyPullbackAffine_apply (c : E) (L : E ≃L[ℝ] E) (z : E) :
    bodyPullbackAffine c L z = bodyPullback c L z := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem bodyPullback_preimage (c : E) (L : E ≃L[ℝ] E) (K : Set E) :
    bodyPullback c L ⁻¹' K = L '' centeredBody c K := by
  ext z
  constructor
  · intro hz
    change c + L.symm z ∈ K at hz
    refine ⟨L.symm z, ?_, L.apply_symm_apply z⟩
    change L.symm z + c ∈ K
    simpa only [add_comm] using hz
  · rintro ⟨x, hx, rfl⟩
    change x + c ∈ K at hx
    simpa only [mem_preimage, bodyPullback_apply, L.symm_apply_apply, add_comm] using hx

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem bodyPullback_image_normalized (c : E) (L : E ≃L[ℝ] E) (K : Set E) :
    bodyPullback c L '' (L '' centeredBody c K) = K := by
  rw [← bodyPullback_preimage]
  exact image_preimage_eq _ (bodyPullback c L).surjective

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem bodyPullback_convex (c : E) (L : E ≃L[ℝ] E) {H : Set E} (hH : Convex ℝ H) :
    Convex ℝ (bodyPullback c L '' H) := by
  exact hH.affine_image (bodyPullbackAffine c L)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem convexOn_bodyPullback (c : E) (L : E ≃L[ℝ] E) {K : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) : ConvexOn ℝ (L '' centeredBody c K) (fun z => f (bodyPullback c L z)) := by
  have h := hf.comp_affineMap (bodyPullbackAffine c L)
  change ConvexOn ℝ (bodyPullback c L ⁻¹' K) (fun z => f (bodyPullback c L z)) at h
  rwa [bodyPullback_preimage] at h

theorem bodyPullback_volume (c : E) (L : E ≃L[ℝ] E) (H : Set E) :
    volume (bodyPullback c L '' H) =
      ENNReal.ofReal |LinearMap.det (L.symm : E →ₗ[ℝ] E)| * volume H := by
  change volume ((fun z => c + L.symm z) '' H) = _
  rw [show (fun z => c + L.symm z) '' H = (fun z => c + z) '' (L.symm '' H) from (image_image _ _ _).symm]
  rw [image_add_left, measure_preimage_add, addHaar_image_continuousLinearEquiv]

theorem bodyPullback_volume_fraction_iff (c : E) (L : E ≃L[ℝ] E) (G H : Set E) (κ : ℝ≥0∞) :
    volume (bodyPullback c L '' H) + κ * volume (bodyPullback c L '' G) ≤
      volume (bodyPullback c L '' G) ↔ volume H + κ * volume G ≤ volume G := by
  rw [bodyPullback_volume, bodyPullback_volume]
  have hfactor := continuous_linear_equiv_volume_factor_pos L.symm
  rw [mul_left_comm κ, ← mul_add]
  exact ENNReal.mul_le_mul_iff_right hfactor.ne' ENNReal.ofReal_ne_top

end
end Nonsmooth
