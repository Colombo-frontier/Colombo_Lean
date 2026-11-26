import MatchingBounds1005.GaussianTensors
import MatchingBounds1005.TensorMasks
import MatchingBounds1005.GaussianBlockGeometry

/-! The actual two Gaussian masks and their joint source norm event. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace MatchingBounds1005.TensorGeometry

theorem tensorForm_smul {d k : ℕ} (c : ℝ) (T : Tensor d k) :
    tensorForm (c • T) = c • tensorForm T := by
  ext v
  simp only [tensorForm_apply, real_inner_smul_left,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

def SourceNormGood (d k : ℕ) : Set (Vec (Fintype.card (Fin k → Fin d))) :=
  {z | ‖tensorForm (gaussianTensor d k z)‖ ≤ sourceGaussianConstant k * Real.sqrt d}

theorem sourceNormGood_measurable (d k : ℕ) : MeasurableSet (SourceNormGood d k) :=
  measurableSet_le (gaussianTensorForm_continuous d k).norm.measurable measurable_const

theorem sourceNormGood_failure {d k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d))).real
      (SourceNormGood d k)ᶜ ≤ 2 * Real.exp (-4 * d) := by
  simpa only [SourceNormGood, Set.compl_setOf, not_le] using
    source_gaussian_norm_failure (d := d) hk1 hk4

def maskSigma (d k : ℕ) (δ : ℝ) : ℝ :=
  δ / (sourceGaussianConstant k * Real.sqrt d)

def scaledGaussianTensor (d k : ℕ) (δ : ℝ)
    (z : Vec (Fintype.card (Fin k → Fin d))) : Tensor d k :=
  maskSigma d k δ • gaussianTensor d k z

theorem scaledGaussianTensor_norm {d k : ℕ} (hd : 0 < d) (hk : 1 ≤ k)
    {δ : ℝ} (hδ : 0 ≤ δ) {z : Vec (Fintype.card (Fin k → Fin d))}
    (hz : z ∈ SourceNormGood d k) :
    ‖tensorForm (scaledGaussianTensor d k δ z)‖ ≤ δ := by
  have hden : 0 < sourceGaussianConstant k * Real.sqrt d :=
    mul_pos (sourceGaussianConstant_pos hk) (Real.sqrt_pos.mpr (by exact_mod_cast hd))
  have hσ : 0 ≤ maskSigma d k δ := div_nonneg hδ hden.le
  rw [scaledGaussianTensor, tensorForm_smul,
    norm_smul (maskSigma d k δ) (tensorForm (gaussianTensor d k z)),
    Real.norm_eq_abs, abs_of_nonneg hσ]
  exact (mul_le_mul_of_nonneg_left hz hσ).trans_eq
    (by unfold maskSigma; exact div_mul_cancel₀ δ hden.ne')

abbrev MaskSeed (d : ℕ) :=
  Vec (Fintype.card (Fin 3 → Fin d)) × Vec (Fintype.card (Fin 4 → Fin d))

def maskLaw (d : ℕ) : Measure (MaskSeed d) :=
  (GaussianVector.standardGaussian _).prod (GaussianVector.standardGaussian _)

instance maskLaw_probability (d : ℕ) : IsProbabilityMeasure (maskLaw d) := by
  unfold maskLaw
  infer_instance

def MaskNormGood (d : ℕ) : Set (MaskSeed d) :=
  {z | z.1 ∈ SourceNormGood d 3 ∧ z.2 ∈ SourceNormGood d 4}

theorem maskNormGood_measurable (d : ℕ) : MeasurableSet (MaskNormGood d) :=
  ((sourceNormGood_measurable d 3).preimage measurable_fst).inter
    ((sourceNormGood_measurable d 4).preimage measurable_snd)

/-- Exactly the manuscript's 1 - 4 exp(-4d) joint event. -/
theorem maskNormGood_probability (d : ℕ) :
    1 - 4 * Real.exp (-4 * d) ≤ (maskLaw d).real (MaskNormGood d) := by
  have hf : MeasurePreserving Prod.fst (maskLaw d) (GaussianVector.standardGaussian
      (Fintype.card (Fin 3 → Fin d))) := ⟨measurable_fst, by simp [maskLaw]⟩
  have hs : MeasurePreserving Prod.snd (maskLaw d) (GaussianVector.standardGaussian
      (Fintype.card (Fin 4 → Fin d))) := ⟨measurable_snd, by simp [maskLaw]⟩
  have h3 := (GaussianBlockGeometry.preserving_failure_le hf
    (SourceNormGood d 3)ᶜ).trans (sourceNormGood_failure (d := d) (by omega : 1 ≤ 3)
      (by omega : 3 ≤ 4))
  have h4 := (GaussianBlockGeometry.preserving_failure_le hs
    (SourceNormGood d 4)ᶜ).trans (sourceNormGood_failure (d := d) (by omega : 1 ≤ 4)
      (by omega : 4 ≤ 4))
  have he : (MaskNormGood d)ᶜ =
      (Prod.fst ⁻¹' (SourceNormGood d 3)ᶜ) ∪ (Prod.snd ⁻¹' (SourceNormGood d 4)ᶜ) := by
    ext z
    simp [MaskNormGood]
    tauto
  have hb : (maskLaw d).real (MaskNormGood d)ᶜ ≤ 4 * Real.exp (-4 * d) := by
    rw [he]
    exact (measureReal_union_le _ _).trans (by linarith)
  have hadd := measureReal_add_measureReal_compl (μ := maskLaw d) (maskNormGood_measurable d)
  rw [measureReal_univ_eq_one] at hadd
  linarith

theorem maskNormGood_bounds {d : ℕ} (hd : 0 < d) {δ₃ δ₄ R : ℝ}
    (h3 : 0 ≤ δ₃) (h4 : 0 ≤ δ₄) (hR : 0 ≤ R) {z : MaskSeed d}
    (hz : z ∈ MaskNormGood d) (x : Vec d) (hx : ‖x‖ ≤ R) :
    let P := mask (scaledGaussianTensor d 3 δ₃ z.1) (scaledGaussianTensor d 4 δ₄ z.2)
    ‖gradient P x‖ ≤ δ₃ * R ^ 2 + δ₄ * R ^ 3 ∧
    |P x| ≤ δ₃ * R ^ 3 / 3 + δ₄ * R ^ 4 / 4 ∧
    |⟪x, gradient P x⟫_ℝ| ≤ R * (δ₃ * R ^ 2 + δ₄ * R ^ 3) := by
  have hb3 := scaledGaussianTensor_norm hd (by omega : 1 ≤ 3) h3 hz.1
  have hb4 := scaledGaussianTensor_norm hd (by omega : 1 ≤ 4) h4 hz.2
  exact ⟨mask_gradient_bound _ _ hb3 hb4 hR x hx,
    mask_value_bound _ _ hb3 hb4 hR x hx, mask_radial_pairing_bound _ _ hb3 hb4 hR x hx⟩

end MatchingBounds1005.TensorGeometry
