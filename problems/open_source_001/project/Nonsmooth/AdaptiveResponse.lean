import Nonsmooth.ContinuousProtocol

open MeasureTheory Function Filter
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem adaptiveLinearInformation_mono (q : ℕ → E → E) : Monotone (adaptiveLinearInformation q) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_sup_left

theorem frameReflection_known {K : Submodule ℝ E} (F : SphericalFrame K)
    {Y : Type} [MeasurableSpace Y] [MeasurableSingletonClass Y] (f : E → Y)
    (hf : @Measurable E Y (frameInformation F) inferInstance f) (x : E) :
    f (frameReflection F x) = f x := by
  have hs := hf (measurableSet_singleton (f x))
  have he := frameReflection_event F hs
  have hx : x ∈ f ⁻¹' {f x} := rfl
  have hx' : x ∈ frameReflection F ⁻¹' (f ⁻¹' {f x}) := by rwa [he]
  exact hx'

theorem frame_known_response {K : Submodule ℝ E} (F : SphericalFrame K) (W : E → E)
    (hW : @Measurable E E (frameInformation F) mE W)
    (hr : @Measurable E ℝ (frameInformation F) inferInstance (fun x => ⟪W x, x⟫_ℝ)) (x : E) :
    ⟪W x, x⟫_ℝ = ⟪W x, framePosterior F x⟫_ℝ := by
  have h := frameReflection_known F (fun x => ⟪W x, x⟫_ℝ) hr x
  rw [frameReflection_known F W hW x, frameReflection_formula, inner_sub_right,
    inner_smul_right] at h
  linarith

theorem spherical_frame_known_response_square {K : Submodule ℝ E} (F : SphericalFrame K) (W : E → E)
    (hW : @Measurable E E (frameInformation F) mE W)
    (hr : @Measurable E ℝ (frameInformation F) inferInstance (fun x => ⟪W x, x⟫_ℝ))
    (hWb : ∀ᵐ x ∂sphericalLaw E, ‖W x‖ ≤ 1) :
    (∫ x : E, ⟪W x, x⟫_ℝ ^ 2 ∂sphericalLaw E) ≤
      (Module.finrank ℝ K : ℝ) / (Module.finrank ℝ E : ℝ) := by
  have hb : ∀ᵐ x ∂sphericalLaw E, ‖⟪W x, x⟫_ℝ‖ ≤ 1 := by
    filter_upwards [hWb, sphericalLaw_unit (E := E)] with x hx hn
    exact (norm_inner_le_norm _ _).trans (by simpa only [hn, mul_one] using hx)
  have hi := (MemLp.of_bound ((hr.mono (frameInformation_le F) le_rfl).aestronglyMeasurable) 1 hb).integrable_sq
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1 (sphericalLaw_unit.mono (fun _ h => h.le))
  have hci := (hV.condExp (by norm_num) (m := frameInformation F)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hle : (∫ x : E, ⟪W x, x⟫_ℝ ^ 2 ∂sphericalLaw E) ≤
      ∫ x : E, ‖((sphericalLaw E)[(fun x : E => x) | frameInformation F]) x‖ ^ 2 ∂sphericalLaw E := by
    apply integral_mono_ae hi _
    · filter_upwards [hWb, spherical_condExp_frame F] with x hx hc
      rw [frame_known_response F W hW hr x, ← hc]
      have hb := (norm_inner_le_norm (𝕜 := ℝ) (W x) (framePosterior F x)).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
      rw [one_mul, Real.norm_eq_abs] at hb
      nlinarith [abs_le.mp hb, sq_abs ⟪W x, framePosterior F x⟫_ℝ]
    · simpa using hci
  rwa [spherical_frame_energy] at hle

theorem spherical_adaptive_response_square (q : ℕ → E → E) (T : ℕ)
    (hT : T ≤ Module.finrank ℝ E)
    (hq : ∀ n < T, @Measurable E E (adaptiveLinearInformation q n) mE (q n))
    {n : ℕ} (hn : n < T) (hqb : ∀ᵐ x ∂sphericalLaw E, ‖q n x‖ ≤ 1) :
    (∫ x : E, ⟪q n x, x⟫_ℝ ^ 2 ∂sphericalLaw E) ≤
      (T : ℝ) / (Module.finrank ℝ E : ℝ) := by
  obtain ⟨K, F, hdim, hinfo⟩ := adaptive_linear_frame q T hT hq
  have hW := (hq n hn).mono ((adaptiveLinearInformation_mono q hn.le).trans hinfo) le_rfl
  have hr : @Measurable E ℝ (frameInformation F) inferInstance (fun x => ⟪q n x, x⟫_ℝ) :=
    (measurable_iff_comap_le.mpr (show MeasurableSpace.comap (fun x => ⟪q n x, x⟫_ℝ) inferInstance ≤
      adaptiveLinearInformation q (n + 1) from le_sup_right)).mono
        ((adaptiveLinearInformation_mono q hn).trans hinfo) le_rfl
  simpa only [hdim] using spherical_frame_known_response_square F (q n) hW hr hqb

end
end Nonsmooth
