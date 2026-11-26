import Nonsmooth.FixedProjection

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem projection_reflection_perpendicular (K : Submodule ℝ E) {w : E}
    (hw : w ∈ Kᗮ) (x : E) :
    K.orthogonalProjection ((ℝ ∙ w)ᗮ.reflection x) = K.orthogonalProjection x := by
  rw [Submodule.reflection_orthogonal_apply, map_neg, Submodule.reflection_singleton_apply,
    map_sub, map_nsmul, map_smul,
    Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hw]
  simp

theorem projection_event_perpendicular_reflection (K : Submodule ℝ E) {w : E}
    (hw : w ∈ Kᗮ) {s : Set E} (hs : MeasurableSet[projectionInformation K] s) :
    (ℝ ∙ w)ᗮ.reflection ⁻¹' s = s := by
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  ext x
  change (K.orthogonalProjection ((ℝ ∙ w)ᗮ.reflection x) : E) ∈ t ↔
    (K.orthogonalProjection x : E) ∈ t
  rw [projection_reflection_perpendicular K hw]

theorem sphericalLaw_restrict_isometry (f : E ≃ₗᵢ[ℝ] E) {s : Set E}
    (hs : MeasurableSet s) (hpre : f ⁻¹' s = s) :
    MeasurePreserving f ((sphericalLaw E).restrict s) ((sphericalLaw E).restrict s) := by
  refine ⟨f.continuous.measurable, ?_⟩
  ext t ht
  rw [Measure.map_apply f.continuous.measurable ht,
    Measure.restrict_apply (f.continuous.measurable ht), Measure.restrict_apply ht]
  have he : f ⁻¹' (t ∩ s) = f ⁻¹' t ∩ s := by rw [Set.preimage_inter, hpre]
  rw [← he, ← Measure.map_apply f.continuous.measurable (ht.inter hs), sphericalLaw_isometry]

/-- On every event determined by a fixed observed subspace, all equally long perpendicular
directions have the same unnormalized second moment. This is a conditional symmetry statement. -/
theorem spherical_perpendicular_event_moments (K : Submodule ℝ E) {u v : E}
    (hu : u ∈ Kᗮ) (hv : v ∈ Kᗮ) (hn : ‖u‖ = ‖v‖) {s : Set E}
    (hs : MeasurableSet[projectionInformation K] s) :
    (∫ x in s, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E) = ∫ x in s, ⟪v, x⟫_ℝ ^ 2 ∂sphericalLaw E := by
  let f : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (u - v))ᗮ.reflection
  have hfu : f u = v := Submodule.reflection_sub hn
  have hpre : f ⁻¹' s = s := projection_event_perpendicular_reflection K (Kᗮ.sub_mem hu hv) hs
  have hpres := sphericalLaw_restrict_isometry f (projectionInformation_le K s hs) hpre
  calc
    _ = ∫ x in s, ⟪v, f x⟫_ℝ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change ⟪u, x⟫_ℝ ^ 2 = ⟪v, f x⟫_ℝ ^ 2
      rw [← hfu, f.inner_map_map]
    _ = _ := hpres.integral_comp f.toMeasurableEquiv.measurableEmbedding
      (fun x : E => ⟪v, x⟫_ℝ ^ 2)

theorem perpendicular_projection_norm_sq (K : Submodule ℝ E) (x : E) :
    ‖(Kᗮ.orthogonalProjection x : E)‖ ^ 2 = ‖x‖ ^ 2 - ‖(K.orthogonalProjection x : E)‖ ^ 2 := by
  have h : ‖x‖ ^ 2 = ‖(K.orthogonalProjection x : E)‖ ^ 2 +
      ‖(Kᗮ.orthogonalProjection x : E)‖ ^ 2 := by
    simpa only [Submodule.coe_norm] using Submodule.norm_sq_eq_add_norm_sq_projection x K
  linarith

theorem spherical_perpendicular_event_second_moment [Nontrivial E] (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) {u : E} (hu : u ∈ Kᗮ) (hun : ‖u‖ = 1)
    {s : Set E} (hs : MeasurableSet[projectionInformation K] s) :
    (∫ x in s, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E) =
      (∫ x in s, 1 - ‖(K.orthogonalProjection x : E)‖ ^ 2 ∂sphericalLaw E) /
        (Module.finrank ℝ Kᗮ : ℝ) := by
  let b := stdOrthonormalBasis ℝ Kᗮ
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hi (i : Fin (Module.finrank ℝ Kᗮ)) :
      Integrable (fun x => ⟪(b i : E), x⟫_ℝ ^ 2) ((sphericalLaw E).restrict s) :=
    ((hV.const_inner (b i : E)).integrable_sq).integrableOn
  have hn (i : Fin (Module.finrank ℝ Kᗮ)) : ‖(b i : E)‖ = 1 := b.orthonormal.1 i
  have he (i : Fin (Module.finrank ℝ Kᗮ)) :
      (∫ x in s, ⟪(b i : E), x⟫_ℝ ^ 2 ∂sphericalLaw E) = ∫ x in s, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E :=
    spherical_perpendicular_event_moments K (b i).property hu ((hn i).trans hun.symm) hs
  have hsum (x : E) : (∑ i, ⟪(b i : E), x⟫_ℝ ^ 2) = ‖(Kᗮ.orthogonalProjection x : E)‖ ^ 2 := by
    simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.coe_norm] using
      b.sum_sq_inner_right (Kᗮ.orthogonalProjection x)
  have htotal : (Module.finrank ℝ Kᗮ : ℝ) * (∫ x in s, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E) =
      ∫ x in s, 1 - ‖(K.orthogonalProjection x : E)‖ ^ 2 ∂sphericalLaw E := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ Kᗮ), ∫ x in s, ⟪(b i : E), x⟫_ℝ ^ 2 ∂sphericalLaw E := by
        simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x in s, ∑ i, ⟪(b i : E), x⟫_ℝ ^ 2 ∂sphericalLaw E :=
        (integral_finset_sum _ (fun i _ => hi i)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (sphericalLaw_unit (E := E))] with x hx
        rw [hsum, perpendicular_projection_norm_sq, hx, one_pow]
  apply (eq_div_iff (Nat.cast_pos.mpr hr).ne').mpr
  simpa only [mul_comm] using htotal

/-- The exact scalar conditional second moment after observing a fixed subspace.
The complementary dimension is positive, and the tested direction is perpendicular and unit. -/
theorem spherical_condExp_perpendicular_square [Nontrivial E] (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) {u : E} (hu : u ∈ Kᗮ) (hun : ‖u‖ = 1) :
    (fun x => (1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ))
      =ᵐ[sphericalLaw E] (sphericalLaw E)[(fun x => ⟪u, x⟫_ℝ ^ 2) | projectionInformation K] := by
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hp : MemLp (fun x => (K.orthogonalProjection x : E)) 2 (sphericalLaw E) :=
    (K.subtypeL.comp K.orthogonalProjection).comp_memLp' hV
  have hpi : Integrable (fun x => ‖(K.orthogonalProjection x : E)‖ ^ 2) (sphericalLaw E) :=
    (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have hg : Integrable (fun x => (1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) /
      (Module.finrank ℝ Kᗮ : ℝ)) (sphericalLaw E) :=
    ((integrable_const (1 : ℝ)).sub hpi).div_const _
  apply ae_eq_condExp_of_forall_setIntegral_eq (projectionInformation_le K)
    (hV.const_inner u).integrable_sq (fun _ _ _ => hg.integrableOn)
  · intro s hs _
    rw [integral_div]
    exact (spherical_perpendicular_event_second_moment K hr hu hun hs).symm
  · have hproj : @Measurable E E (projectionInformation K) mE
        (fun x => (K.orthogonalProjection x : E)) := measurable_iff_comap_le.mpr le_rfl
    have hout : Measurable (fun x : E => (1 - ‖x‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ)) :=
      ((measurable_const.sub (measurable_id.norm.pow_const 2)).div_const _)
    exact (hout.comp hproj).aestronglyMeasurable

theorem spherical_condExp_perpendicular_square_general [Nontrivial E] (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) {u : E} (hu : u ∈ Kᗮ) :
    (fun x => ‖u‖ ^ 2 * ((1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ)))
      =ᵐ[sphericalLaw E] (sphericalLaw E)[(fun x => ⟪u, x⟫_ℝ ^ 2) | projectionInformation K] := by
  by_cases hu0 : u = 0
  · subst u
    simp only [norm_zero, inner_zero_left, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    change (0 : E → ℝ) =ᵐ[sphericalLaw E] (sphericalLaw E)[(0 : E → ℝ) | projectionInformation K]
    rw [condExp_zero]
  have hnu : normalizedDirection u ∈ Kᗮ := Kᗮ.smul_mem _ hu
  have hn := normalizedDirection_norm hu0
  have he : ‖u‖ • normalizedDirection u = u := by
    simp [normalizedDirection, smul_smul, norm_ne_zero_iff.mpr hu0]
  have hfun : (fun x => ⟪u, x⟫_ℝ ^ 2) =
      ‖u‖ ^ 2 • (fun x => ⟪normalizedDirection u, x⟫_ℝ ^ 2) := by
    funext x
    conv_lhs => rw [← he, real_inner_smul_left, mul_pow]
    rfl
  have hc := spherical_condExp_perpendicular_square K hr hnu hn
  have hs := condExp_smul (μ := sphericalLaw E) (‖u‖ ^ 2)
    (fun x => ⟪normalizedDirection u, x⟫_ℝ ^ 2) (projectionInformation K)
  rw [hfun]
  filter_upwards [hc, hs] with x hcx hsx
  change ‖u‖ ^ 2 * ((1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ)) = _
  rw [hsx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← hcx]

/-- Conditional covariance in the unobserved subspace, derived by polarization. -/
theorem spherical_condExp_perpendicular_product [Nontrivial E] (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) {u v : E} (hu : u ∈ Kᗮ) (hv : v ∈ Kᗮ) :
    (fun x => ⟪u, v⟫_ℝ * ((1 - ‖(K.orthogonalProjection x : E)‖ ^ 2) / (Module.finrank ℝ Kᗮ : ℝ)))
      =ᵐ[sphericalLaw E] (sphericalLaw E)[(fun x => ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ) | projectionInformation K] := by
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hsum := spherical_condExp_perpendicular_square_general K hr (Kᗮ.add_mem hu hv)
  have hU := spherical_condExp_perpendicular_square_general K hr hu
  have hW := spherical_condExp_perpendicular_square_general K hr hv
  let A : E → ℝ := fun x => ⟪u + v, x⟫_ℝ ^ 2
  let B : E → ℝ := fun x => ⟪u, x⟫_ℝ ^ 2
  let C : E → ℝ := fun x => ⟪v, x⟫_ℝ ^ 2
  have hAi : Integrable A (sphericalLaw E) := (hV.const_inner (u + v)).integrable_sq
  have hBi : Integrable B (sphericalLaw E) := (hV.const_inner u).integrable_sq
  have hCi : Integrable C (sphericalLaw E) := (hV.const_inner v).integrable_sq
  have he : (fun x => ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ) = (1 / 2 : ℝ) • (A - B - C) := by
    funext x
    change ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ = (1 / 2 : ℝ) • (A x - B x - C x)
    simp only [A, B, C, inner_add_left, smul_eq_mul]
    ring
  have hs₁ := condExp_sub hAi hBi (projectionInformation K)
  have hs₂ := condExp_sub (hAi.sub hBi) hCi (projectionInformation K)
  have hhalf := condExp_smul (μ := sphericalLaw E) (1 / 2 : ℝ)
    (A - B - C) (projectionInformation K)
  rw [he]
  filter_upwards [hsum, hU, hW, hs₁, hs₂, hhalf] with x hsumx hUx hWx hs₁x hs₂x hhx
  rw [hhx]
  change _ = (1 / 2 : ℝ) • ((sphericalLaw E)[A - B - C | projectionInformation K] x)
  rw [hs₂x]
  simp only [Pi.sub_apply]
  rw [hs₁x]
  simp only [Pi.sub_apply, smul_eq_mul]
  change _ = (1 / 2 : ℝ) * ((sphericalLaw E)[(fun x => ⟪u + v, x⟫_ℝ ^ 2) | projectionInformation K] x -
    (sphericalLaw E)[(fun x => ⟪u, x⟫_ℝ ^ 2) | projectionInformation K] x -
    (sphericalLaw E)[(fun x => ⟪v, x⟫_ℝ ^ 2) | projectionInformation K] x)
  rw [← hsumx, ← hUx, ← hWx, norm_add_sq_real]
  ring

/-- The fixed-subspace version of the manuscript's residual-variance formula, written with
the actual posterior mean and the original remaining-dimension denominator. -/
theorem spherical_condExp_residual_variance [Nontrivial E] (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) {u : E} (hu : u ∈ Kᗮ) (hun : ‖u‖ = 1) :
    (fun x => (1 - ‖((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x‖ ^ 2) /
      ((Module.finrank ℝ E : ℝ) - (Module.finrank ℝ K : ℝ))) =ᵐ[sphericalLaw E]
      (sphericalLaw E)[(fun x => ⟪x - ((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x,
        u⟫_ℝ ^ 2) | projectionInformation K] := by
  have hdim : (Module.finrank ℝ E : ℝ) - (Module.finrank ℝ K : ℝ) =
      (Module.finrank ℝ Kᗮ : ℝ) := by
    have h : (Module.finrank ℝ K : ℝ) + (Module.finrank ℝ Kᗮ : ℝ) =
        (Module.finrank ℝ E : ℝ) := by exact_mod_cast K.finrank_add_finrank_orthogonal
    linarith
  have hmean := spherical_condExp_projection K
  have hfun : (fun x => ⟪x - ((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x,
      u⟫_ℝ ^ 2) =ᵐ[sphericalLaw E] (fun x => ⟪u, x⟫_ℝ ^ 2) := by
    filter_upwards [hmean] with x hx
    change ⟪x - ((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x, u⟫_ℝ ^ 2 = _
    have horth : ⟪(K.orthogonalProjection x : E), u⟫_ℝ = 0 :=
      (K.mem_orthogonal u).mp hu _ (K.orthogonalProjection x).property
    rw [← hx, inner_sub_left, horth, sub_zero, real_inner_comm]
  have hce := condExp_congr_ae (m := projectionInformation K) hfun
  have hs := spherical_condExp_perpendicular_square K hr hu hun
  filter_upwards [hmean, hce, hs] with x hx hcx hsx
  rw [hdim]
  change (1 - ‖((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x‖ ^ 2) /
    (Module.finrank ℝ Kᗮ : ℝ) = _
  rw [← hx, hcx]
  exact hsx

end
end Nonsmooth
