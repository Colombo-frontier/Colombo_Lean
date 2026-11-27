import Nonsmooth.SphericalLaw

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def projectionInformation (K : Submodule ℝ E) : MeasurableSpace E :=
  MeasurableSpace.comap (fun x => (K.orthogonalProjection x : E)) mE

theorem projectionInformation_le (K : Submodule ℝ E) : projectionInformation K ≤ mE :=
  measurable_iff_comap_le.mp (K.subtypeL.comp K.orthogonalProjection).continuous.measurable

theorem orthogonalProjection_reflection (K : Submodule ℝ E) (x : E) :
    K.orthogonalProjection (K.reflection x) = K.orthogonalProjection x := by
  rw [Submodule.reflection_apply, Submodule.starProjection_apply, map_sub, map_nsmul,
    Submodule.orthogonalProjection_mem_subspace_eq_self]
  module

theorem projection_event_reflection (K : Submodule ℝ E) {s : Set E}
    (hs : MeasurableSet[projectionInformation K] s) : K.reflection ⁻¹' s = s := by
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  ext x
  change (K.orthogonalProjection (K.reflection x) : E) ∈ t ↔ (K.orthogonalProjection x : E) ∈ t
  rw [orthogonalProjection_reflection]

theorem sphericalLaw_identity_integrable [Nontrivial E] :
    Integrable (fun x : E => x) (sphericalLaw E) := by
  apply (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable
  filter_upwards [sphericalLaw_unit (E := E)] with x hx
  exact hx.le

theorem spherical_projection_setIntegral [Nontrivial E] (K : Submodule ℝ E) {s : Set E}
    (hs : MeasurableSet[projectionInformation K] s) :
    (∫ x in s, (K.orthogonalProjection x : E) ∂sphericalLaw E) =
      ∫ x in s, x ∂sphericalLaw E := by
  have hsm : MeasurableSet s := projectionInformation_le K s hs
  have hpre := projection_event_reflection K hs
  have hfun : (fun x => s.indicator (fun y : E => y) (K.reflection x)) =
      s.indicator (fun x => K.reflection x) := by
    funext x
    have hmem : K.reflection x ∈ s ↔ x ∈ s := by
      change x ∈ K.reflection ⁻¹' s ↔ x ∈ s
      rw [hpre]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]
  have h := (sphericalLaw_measurePreserving K.reflection).integral_comp
    K.reflection.toMeasurableEquiv.measurableEmbedding (s.indicator (fun y : E => y))
  rw [hfun, integral_indicator hsm, integral_indicator hsm] at h
  have hi := sphericalLaw_identity_integrable (E := E)
  have hp : Integrable (fun x => (K.orthogonalProjection x : E)) (sphericalLaw E) :=
    (K.subtypeL.comp K.orthogonalProjection).integrable_comp hi
  simp only [Submodule.reflection_apply, Submodule.starProjection_apply, two_smul] at h
  have hpp : Integrable (fun x => (K.orthogonalProjection x : E) + (K.orthogonalProjection x : E))
      (sphericalLaw E) := hp.add hp
  rw [integral_sub hpp.integrableOn hi.integrableOn,
    integral_add hp.integrableOn hp.integrableOn] at h
  have he : (2 : ℝ) • (∫ x in s, (K.orthogonalProjection x : E) ∂sphericalLaw E) =
      (2 : ℝ) • (∫ x in s, x ∂sphericalLaw E) := by
    simpa only [two_smul] using sub_eq_iff_eq_add.mp h
  exact (smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)) he

/-- For a fixed observed subspace, the actual spherical posterior mean is its orthogonal
projection. This proves the nonadaptive posterior identity, without assuming a conditional law. -/
theorem spherical_condExp_projection [Nontrivial E] (K : Submodule ℝ E) :
    (fun x : E => (K.orthogonalProjection x : E)) =ᵐ[sphericalLaw E]
      (sphericalLaw E)[(fun x : E => x) | projectionInformation K] := by
  have hi := sphericalLaw_identity_integrable (E := E)
  have hp : Integrable (fun x => (K.orthogonalProjection x : E)) (sphericalLaw E) :=
    (K.subtypeL.comp K.orthogonalProjection).integrable_comp hi
  apply ae_eq_condExp_of_forall_setIntegral_eq (projectionInformation_le K) hi
    (fun _ _ _ => hp.integrableOn) (fun _ hs _ => spherical_projection_setIntegral K hs)
  have hm : @Measurable E E (projectionInformation K) mE
      (fun x => (K.orthogonalProjection x : E)) := measurable_iff_comap_le.mpr le_rfl
  exact hm.aestronglyMeasurable

theorem spherical_projection_second_moment [Nontrivial E] (K : Submodule ℝ E) :
    (∫ x, ‖(K.orthogonalProjection x : E)‖ ^ 2 ∂sphericalLaw E) =
      (Module.finrank ℝ K : ℝ) / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ K
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hi (i : Fin (Module.finrank ℝ K)) :
      Integrable (fun x => ⟪(b i : E), x⟫_ℝ ^ 2) (sphericalLaw E) :=
    (hV.const_inner (b i : E)).integrable_sq
  have hn (i : Fin (Module.finrank ℝ K)) : ‖(b i : E)‖ = 1 := b.orthonormal.1 i
  have hs (x : E) : (∑ i, ⟪(b i : E), x⟫_ℝ ^ 2) = ‖(K.orthogonalProjection x : E)‖ ^ 2 := by
    have h := b.sum_sq_norm_inner_right (K.orthogonalProjection x)
    simpa only [Real.norm_eq_abs, sq_abs,
      Submodule.inner_orthogonalProjection_eq_of_mem_left, ← Submodule.coe_norm] using h
  calc
    _ = ∫ x, ∑ i, ⟪(b i : E), x⟫_ℝ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (hs x).symm)
    _ = ∑ i : Fin (Module.finrank ℝ K), ∫ x, ⟪(b i : E), x⟫_ℝ ^ 2 ∂sphericalLaw E :=
      integral_finset_sum _ (fun i _ => hi i)
    _ = _ := by
      simp only [sphericalLaw_unit_second_moment (hn _), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Exact posterior energy after observing a fixed subspace, including redundant fixed queries. -/
theorem spherical_condExp_projection_energy [Nontrivial E] (K : Submodule ℝ E) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | projectionInformation K]) x‖ ^ 2 ∂sphericalLaw E) =
      (Module.finrank ℝ K : ℝ) / (Module.finrank ℝ E : ℝ) := by
  calc
    _ = ∫ x, ‖(K.orthogonalProjection x : E)‖ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      filter_upwards [spherical_condExp_projection K] with x hx
      rw [← hx]
    _ = _ := spherical_projection_second_moment K

theorem spherical_condExp_subinformation_energy [Nontrivial E] (K : Submodule ℝ E)
    {m : MeasurableSpace E} (hm : m ≤ projectionInformation (mE := mE) K) :
    (∫ x, ‖((@sphericalLaw E _ _ mE _ _)[(fun x : E => x) | m]) x‖ ^ 2
      ∂(@sphericalLaw E _ _ mE _ _)) ≤
      (Module.finrank ℝ K : ℝ) / (Module.finrank ℝ E : ℝ) := by
  letI : MeasurableSpace E := mE
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have h := condExp_second_moment_mono hm (projectionInformation_le K) hV
  rwa [spherical_condExp_projection_energy] at h

def fixedLinearInformation {T : ℕ} (q : Fin T → E) : MeasurableSpace E :=
  MeasurableSpace.comap (fun x i => ⟪q i, x⟫_ℝ) inferInstance

theorem fixedLinearInformation_le_projection {T : ℕ} (q : Fin T → E) :
    fixedLinearInformation q ≤ projectionInformation (Submodule.span ℝ (Set.range q)) := by
  let K := Submodule.span ℝ (Set.range q)
  have hp : @Measurable E E (projectionInformation K) mE
      (fun x => (K.orthogonalProjection x : E)) := measurable_iff_comap_le.mpr le_rfl
  have hf : Measurable (fun x : E => fun i => ⟪q i, x⟫_ℝ) :=
    measurable_pi_lambda _ (fun i => (continuous_const.inner continuous_id).measurable)
  have hcomp : @Measurable E (Fin T → ℝ) (projectionInformation K) inferInstance
      (fun x i => ⟪q i, (K.orthogonalProjection x : E)⟫_ℝ) := hf.comp hp
  have he : (fun x i => ⟪q i, (K.orthogonalProjection x : E)⟫_ℝ) =
      (fun x i => ⟪q i, x⟫_ℝ) := by
    funext x i
    have hqi : q i ∈ K := Submodule.subset_span (Set.mem_range_self i)
    simpa only [Submodule.coe_inner] using
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (⟨q i, hqi⟩ : K) x)
  rw [he] at hcomp
  exact measurable_iff_comap_le.mp hcomp

/-- The manuscript's posterior-energy bound is fully proved for every fixed family of queries,
including zero or linearly dependent query vectors. Adaptively selected queries remain separate. -/
theorem spherical_fixed_queries_energy [Nontrivial E] {T : ℕ} (q : Fin T → E) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | fixedLinearInformation q]) x‖ ^ 2 ∂sphericalLaw E) ≤
      min ((T : ℝ) / (Module.finrank ℝ E : ℝ)) 1 := by
  let K := Submodule.span ℝ (Set.range q)
  have h := spherical_condExp_subinformation_energy K (fixedLinearInformation_le_projection q)
  have hcard : Module.finrank ℝ K ≤ T := by
    simpa [K, Set.finrank] using (finrank_range_le_card (R := ℝ) q)
  have hdim : Module.finrank ℝ K ≤ Module.finrank ℝ E := Submodule.finrank_le K
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  apply h.trans
  apply le_min
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hd.le
  · exact (div_le_one hd).mpr (by exact_mod_cast hdim)

end
end Nonsmooth
