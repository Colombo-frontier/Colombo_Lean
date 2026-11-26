import Nonsmooth.WeightedExpectation

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The direction may depend measurably on all observations in the fixed subspace K. -/
theorem spherical_adapted_direction_square (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ ≤ 1) :
    (fun x => ((1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ)) * ‖U x‖ ^ 2)
      =ᵐ[sphericalLaw E] (sphericalLaw E)[(fun x => ⟪U x, x⟫_ℝ ^ 2) | projectionInformation K] := by
  let b := stdOrthonormalBasis ℝ Kᗮ
  let r : Fin (Module.finrank ℝ Kᗮ) → E → ℝ := fun i x => ⟪(b i : E), x⟫_ℝ
  let c : Fin (Module.finrank ℝ Kᗮ) → E → ℝ := fun i x => ⟪(b i : E), U x⟫_ℝ
  let a : E → ℝ := fun x => (1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ)
  have hb (i : Fin (Module.finrank ℝ Kᗮ)) : ‖(b i : E)‖ = 1 := b.orthonormal.1 i
  have hrm (i : Fin (Module.finrank ℝ Kᗮ)) : AEStronglyMeasurable (r i) (sphericalLaw E) :=
    (continuous_const.inner continuous_id).measurable.aestronglyMeasurable
  have hcm (i : Fin (Module.finrank ℝ Kᗮ)) :
      AEStronglyMeasurable[projectionInformation K] (c i) (sphericalLaw E) :=
    ((continuous_const.inner continuous_id).measurable.comp hU).aestronglyMeasurable
  have hrb (i : Fin (Module.finrank ℝ Kᗮ)) : ∀ᵐ x ∂sphericalLaw E, ‖r i x‖ ≤ 1 := by
    filter_upwards [sphericalLaw_unit (E := E)] with x hx
    have h := norm_inner_le_norm (𝕜 := ℝ) (b i : E) x
    simpa only [r, hb i, hx, one_mul] using h
  have hcb (i : Fin (Module.finrank ℝ Kᗮ)) : ∀ᵐ x ∂sphericalLaw E, ‖c i x‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro x
    have h := norm_inner_le_norm (𝕜 := ℝ) (b i : E) (U x)
    rw [hb i, one_mul] at h
    exact h.trans (hUn x)
  have hcov (i j : Fin (Module.finrank ℝ Kᗮ)) :
      (sphericalLaw E)[(fun x => r i x * r j x) | projectionInformation K] =ᵐ[sphericalLaw E]
        if i = j then a else 0 := by
    have h := spherical_condExp_perpendicular_product K hr (b i).property (b j).property
    have hij : ⟪(b i : E), (b j : E)⟫_ℝ = if i = j then 1 else 0 :=
      (orthonormal_iff_ite.mp b.orthonormal) i j
    filter_upwards [h] with x hx
    change (sphericalLaw E)[(fun x => ⟪(b i : E), x⟫_ℝ * ⟪(b j : E), x⟫_ℝ) | projectionInformation K] x = _
    rw [← hx, hij]
    by_cases he : i = j <;> simp [he, a]
  have hpair (x : E) : (∑ i, c i x * r i x) = ⟪U x, x⟫_ℝ := by
    let ux : Kᗮ := ⟨U x, hUp x⟩
    have h := b.sum_inner_mul_inner ux (Kᗮ.orthogonalProjection x)
    simp only [Submodule.inner_orthogonalProjection_eq_of_mem_left] at h
    change (∑ i, ⟪U x, (b i : E)⟫_ℝ * ⟪(b i : E), x⟫_ℝ) = ⟪U x, x⟫_ℝ at h
    simpa only [c, r, real_inner_comm (U x)] using h
  have hsq (x : E) : (∑ i, c i x ^ 2) = ‖U x‖ ^ 2 := by
    let ux : Kᗮ := ⟨U x, hUp x⟩
    simpa only [c, Submodule.coe_inner, Submodule.coe_norm, ux] using b.sum_sq_inner_right ux
  have h := condExp_quadratic_of_scalar_covariance (projectionInformation_le K) r c a hrm hcm hrb hcb hcov
  simpa only [hpair, hsq] using h

theorem spherical_adapted_unit_direction_square (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) :
    (fun x => (1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ))
      =ᵐ[sphericalLaw E] (sphericalLaw E)[(fun x => ⟪U x, x⟫_ℝ ^ 2) | projectionInformation K] := by
  simpa only [hUn, one_pow, mul_one] using spherical_adapted_direction_square K hr U hU hUp
    (fun x => (hUn x).le)

/-- The actual posterior residual also permits a direction selected from the fixed observations. -/
theorem spherical_adapted_residual_variance (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) :
    (fun x => (1 - ‖((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x‖ ^ 2) /
      ((Module.finrank ℝ E : ℝ) - (Module.finrank ℝ K : ℝ))) =ᵐ[sphericalLaw E]
      (sphericalLaw E)[(fun x => ⟪x - ((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x,
        U x⟫_ℝ ^ 2) | projectionInformation K] := by
  have hdim : (Module.finrank ℝ E : ℝ) - (Module.finrank ℝ K : ℝ) =
      (Module.finrank ℝ Kᗮ : ℝ) := by
    have h : (Module.finrank ℝ K : ℝ) + (Module.finrank ℝ Kᗮ : ℝ) =
        (Module.finrank ℝ E : ℝ) := by exact_mod_cast K.finrank_add_finrank_orthogonal
    linarith
  have hmean := spherical_condExp_projection K
  have hfun : (fun x => ⟪x - ((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x,
      U x⟫_ℝ ^ 2) =ᵐ[sphericalLaw E] (fun x => ⟪U x, x⟫_ℝ ^ 2) := by
    filter_upwards [hmean] with x hx
    change ⟪x - ((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x, U x⟫_ℝ ^ 2 = _
    have horth : ⟪(K.orthogonalProjection x : E), U x⟫_ℝ = 0 :=
      (K.mem_orthogonal (U x)).mp (hUp x) _ (K.orthogonalProjection x).property
    rw [← hx, inner_sub_left, horth, sub_zero, real_inner_comm]
  have hce := condExp_congr_ae (m := projectionInformation K) hfun
  have hs := spherical_adapted_unit_direction_square K hr U hU hUp hUn
  filter_upwards [hmean, hce, hs] with x hx hcx hsx
  rw [hdim]
  change (1 - ‖((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x‖ ^ 2) /
    (Module.finrank ℝ Kᗮ : ℝ) = _
  rw [← hx, hcx]
  exact hsx

/-- A unit query orthogonal to a fixed observed space has unconditional energy exactly 1/d,
even when its direction is selected measurably from those observations. -/
theorem spherical_adapted_unit_direction_second_moment (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) :
    (∫ x, ⟪U x, x⟫_ℝ ^ 2 ∂sphericalLaw E) = 1 / (Module.finrank ℝ E : ℝ) := by
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hp : MemLp (fun x => (K.orthogonalProjection x : E)) 2 (sphericalLaw E) :=
    (K.subtypeL.comp K.orthogonalProjection).comp_memLp' hV
  have hpi : Integrable (fun x => ‖(K.orthogonalProjection x : E)‖ ^ 2) (sphericalLaw E) :=
    (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have hdim : (Module.finrank ℝ K : ℝ) + (Module.finrank ℝ Kᗮ : ℝ) =
      (Module.finrank ℝ E : ℝ) := by exact_mod_cast K.finrank_add_finrank_orthogonal
  have hr' : (Module.finrank ℝ Kᗮ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr)
  have hd' : (Module.finrank ℝ E : ℝ) ≠ 0 := ne_of_gt (by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E))
  calc
    _ = ∫ x, ((sphericalLaw E)[(fun x => ⟪U x, x⟫_ℝ ^ 2) | projectionInformation K]) x
        ∂sphericalLaw E := (integral_condExp (projectionInformation_le K)).symm
    _ = ∫ x, (1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ)
        ∂sphericalLaw E := integral_congr_ae
          (spherical_adapted_unit_direction_square K hr U hU hUp hUn).symm
    _ = (1 - (Module.finrank ℝ K : ℝ) / (Module.finrank ℝ E : ℝ)) /
        (Module.finrank ℝ Kᗮ : ℝ) := by
      rw [integral_div, integral_sub (integrable_const _) hpi,
        integral_const, spherical_projection_second_moment]
      simp
    _ = _ := by field_simp; nlinarith

end
end Nonsmooth
