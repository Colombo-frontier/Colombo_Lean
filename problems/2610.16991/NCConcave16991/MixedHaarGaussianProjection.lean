import NCConcave16991.MixedHaarSphereGaussian
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # The actual standard Gaussian projection law on a finite-dimensional subspace -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem dual_comp_orthogonalProjection_norm (D : Submodule ℝ E) (L : StrongDual ℝ D) :
    ‖L.comp D.orthogonalProjectionOnto‖ = ‖L‖ := by
  apply le_antisymm
  · calc
      _ ≤ ‖L‖ * ‖D.orthogonalProjectionOnto‖ := L.opNorm_comp_le _
      _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left D.orthogonalProjectionOnto_norm_le (norm_nonneg L)
      _ = _ := mul_one _
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro x
    simpa only [ContinuousLinearMap.comp_apply,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.norm_coe] using (L.comp D.orthogonalProjectionOnto).le_opNorm (x : E)

/-- The image is the actual standard Gaussian of the subspace, proved by
equality of characteristic functions and the exact dual norm. -/
theorem stdGaussian_map_orthogonalProjectionOnto (D : Submodule ℝ E) :
    (stdGaussian E).map D.orthogonalProjectionOnto = stdGaussian D := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map,charFunDual_stdGaussian,charFunDual_stdGaussian,
    dual_comp_orthogonalProjection_norm]

theorem orthogonalProjection_stdGaussian_preserving (D : Submodule ℝ E) :
    MeasurePreserving D.orthogonalProjectionOnto (stdGaussian E) (stdGaussian D) :=
  ⟨D.orthogonalProjectionOnto.continuous.measurable,stdGaussian_map_orthogonalProjectionOnto D⟩

theorem stdGaussian_projection_ne_zero_ae_of_unit (D : Submodule ℝ E) (e : D) (he : ‖e‖ = 1) :
    ∀ᵐ g ∂stdGaussian E, D.orthogonalProjectionOnto g ≠ 0 :=
  (orthogonalProjection_stdGaussian_preserving D).quasiMeasurePreserving.ae
    (stdGaussian_ne_zero_ae e he)

theorem stdGaussian_projection_ne_zero_ae (D : Submodule ℝ E)
    (hdim : 0 < Module.finrank ℝ D) :
    ∀ᵐ g ∂stdGaussian E, D.orthogonalProjectionOnto g ≠ 0 := by
  letI := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨v,hv⟩ := exists_ne (0 : D)
  exact stdGaussian_projection_ne_zero_ae_of_unit D (normalize v) (normalize_norm hv)

theorem stdGaussian_orthogonal_residual_ne_zero_ae (D : Submodule ℝ E)
    (hdim : 0 < Module.finrank ℝ Dᗮ) :
    ∀ᵐ g ∂stdGaussian E, g - D.starProjection g ≠ 0 := by
  filter_upwards [stdGaussian_projection_ne_zero_ae Dᗮ hdim] with g hg
  intro hz
  apply hg
  apply Subtype.ext
  simpa only [Submodule.coe_orthogonalProjectionOnto_apply,Submodule.starProjection_orthogonal_val,
    Submodule.coe_zero] using hz

end NCConcave16991.MixedHaar
