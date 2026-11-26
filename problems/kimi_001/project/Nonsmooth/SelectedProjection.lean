import Nonsmooth.AdaptedDirection

open MeasureTheory Function
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem projectionInformation_mono {K L : Submodule ℝ E} (hKL : K ≤ L) :
    projectionInformation (mE := mE) K ≤ projectionInformation (mE := mE) L := by
  have hL : @Measurable E E (projectionInformation L) mE
      (fun x => (L.orthogonalProjection x : E)) := measurable_iff_comap_le.mpr le_rfl
  have hK : Measurable (fun x => (K.orthogonalProjection x : E)) :=
    (K.subtypeL.comp K.orthogonalProjection).continuous.measurable
  have h := hK.comp hL
  have hnest (x : E) : (K.orthogonalProjection (L.orthogonalProjection x) : E) =
      (K.orthogonalProjection x : E) :=
    congrArg Subtype.val (Submodule.orthogonalProjectionOnto_starProjection_of_le hKL x)
  simp only [Function.comp_def, hnest] at h
  exact measurable_iff_comap_le.mp h

variable {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def selectedProjection (K : ι → Submodule ℝ E) (choice : E → ι) (x : E) : E :=
  ((K (choice x)).orthogonalProjection x : E)

def selectedProjectionInformation (K : ι → Submodule ℝ E) (choice : E → ι) : MeasurableSpace E :=
  MeasurableSpace.comap (fun x => (choice x, selectedProjection K choice x)) inferInstance

theorem selectedProjection_measurable (K : ι → Submodule ℝ E) {choice : E → ι}
    (hc : Measurable choice) : Measurable (selectedProjection K choice) := by
  have hp : Measurable (fun p : E × ι => ((K p.2).orthogonalProjection p.1 : E)) :=
    measurable_from_prod_countable_left (fun i =>
      ((K i).subtypeL.comp (K i).orthogonalProjection).continuous.measurable)
  convert! hp.comp (measurable_id.prodMk hc) using 1

theorem selectedProjectionInformation_le (K : ι → Submodule ℝ E) {choice : E → ι}
    (hc : Measurable choice) : selectedProjectionInformation K choice ≤ mE :=
  measurable_iff_comap_le.mp (hc.prodMk (selectedProjection_measurable K hc))

/-- Each branch must be identifiable using the projection on that branch's observed space. -/
theorem selectedProjection_event_piece (K : ι → Submodule ℝ E) (choice : E → ι)
    (hbranch : ∀ i, MeasurableSet[projectionInformation (K i)] {x | choice x = i})
    {s : Set E} (hs : MeasurableSet[selectedProjectionInformation K choice] s) (i : ι) :
    MeasurableSet[projectionInformation (K i)] (s ∩ {x | choice x = i}) := by
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hp : @Measurable E E (projectionInformation (K i)) mE
      (fun x => ((K i).orthogonalProjection x : E)) := measurable_iff_comap_le.mpr le_rfl
  have hm := ((measurable_const (a := i)).prodMk hp) ht
  have he : (fun x => (choice x, selectedProjection K choice x)) ⁻¹' t ∩ {x | choice x = i} =
      (fun x => (i, ((K i).orthogonalProjection x : E))) ⁻¹' t ∩ {x | choice x = i} := by
    ext x
    by_cases hx : choice x = i
    · simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hx, and_true]
      have hp : selectedProjection K choice x = ((K i).orthogonalProjection x : E) :=
        congrArg (fun j : ι => ((K j).orthogonalProjection x : E)) hx
      rw [hp]
    · simp [hx]
  rw [he]
  exact hm.inter (hbranch i)

theorem selectedProjection_integrable [Nontrivial E] (K : ι → Submodule ℝ E)
    {choice : E → ι} (hc : Measurable choice) :
    Integrable (selectedProjection K choice) (sphericalLaw E) := by
  apply sphericalLaw_identity_integrable.norm.mono'
    (selectedProjection_measurable K hc).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hb := mul_le_mul_of_nonneg_right
    (Submodule.orthogonalProjection_norm_le (K (choice x))) (norm_nonneg x)
  rw [one_mul] at hb
  exact ((K (choice x)).orthogonalProjection.le_opNorm x).trans hb

/-- A countable, observation-dependent choice of subspace has the actual piecewise projection
as posterior mean, provided each branch is recognizable from that branch's observations. -/
theorem spherical_condExp_selectedProjection [Nontrivial E] (K : ι → Submodule ℝ E)
    {choice : E → ι} (hc : Measurable choice)
    (hbranch : ∀ i, MeasurableSet[projectionInformation (K i)] {x | choice x = i}) :
    selectedProjection K choice =ᵐ[sphericalLaw E]
      (sphericalLaw E)[(fun x : E => x) | selectedProjectionInformation K choice] := by
  have hi := sphericalLaw_identity_integrable (E := E)
  have hp := selectedProjection_integrable K hc
  apply ae_eq_condExp_of_forall_setIntegral_eq (selectedProjectionInformation_le K hc) hi
    (fun _ _ _ => hp.integrableOn)
  · intro s hs _
    let pieces : ι → Set E := fun i => s ∩ {x | choice x = i}
    have hmeas (i : ι) : MeasurableSet (pieces i) :=
      projectionInformation_le (K i) _ (selectedProjection_event_piece K choice hbranch hs i)
    have hdis : Pairwise (Disjoint on pieces) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact hij (hxi.2.symm.trans hxj.2)
    have hcover : (⋃ i, pieces i) = s := by
      ext x
      simp only [pieces, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨choice x, hx, rfl⟩⟩
    rw [← hcover, integral_iUnion hmeas hdis hp.integrableOn,
      integral_iUnion hmeas hdis hi.integrableOn]
    apply tsum_congr
    intro i
    calc
      _ = ∫ x in pieces i, ((K i).orthogonalProjection x : E) ∂sphericalLaw E := by
        apply setIntegral_congr_fun (hmeas i)
        intro x hx
        exact congrArg (fun j : ι => ((K j).orthogonalProjection x : E)) hx.2
      _ = _ := spherical_projection_setIntegral (K i)
        (selectedProjection_event_piece K choice hbranch hs i)
  · have hpair : @Measurable E (ι × E) (selectedProjectionInformation K choice) inferInstance
        (fun x => (choice x, selectedProjection K choice x)) := measurable_iff_comap_le.mpr le_rfl
    exact hpair.snd.aestronglyMeasurable

/-- Observing K first and then choosing one of countably many extensions is a concrete
instance of the branch condition; no conditional distribution is assumed. -/
theorem spherical_condExp_selected_extension [Nontrivial E] (K : Submodule ℝ E)
    (L : ι → Submodule ℝ E) (hKL : ∀ i, K ≤ L i) (choice : E → ι)
    (hc : @Measurable E ι (projectionInformation K) inferInstance choice) :
    selectedProjection L choice =ᵐ[sphericalLaw E]
      (sphericalLaw E)[(fun x : E => x) | selectedProjectionInformation L choice] := by
  apply spherical_condExp_selectedProjection L (hc.mono (projectionInformation_le K) le_rfl)
  intro i
  exact projectionInformation_mono (hKL i) _ (hc (measurableSet_singleton i))

/-- Adding one perpendicular unit direction gives an explicit orthogonal projection. -/
theorem orthogonalProjection_unit_extension (K : Submodule ℝ E) {u : E}
    (hu : u ∈ Kᗮ) (hun : ‖u‖ = 1) (x : E) :
    ((K ⊔ ℝ ∙ u).orthogonalProjection x : E) =
      (K.orthogonalProjection x : E) + ⟪u, x⟫_ℝ • u := by
  change (K ⊔ ℝ ∙ u).starProjection x = _
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact Submodule.add_mem_sup (K.orthogonalProjection x).property
      ((ℝ ∙ u).smul_mem _ (Submodule.mem_span_singleton_self u))
  · rw [← Submodule.inf_orthogonal]
    constructor
    · have h := Kᗮ.sub_mem (K.sub_starProjection_mem_orthogonal x) (Kᗮ.smul_mem ⟪u, x⟫_ℝ hu)
      convert! h using 1 <;> simp only [sub_sub, Submodule.starProjection_apply]
    · change x - ((K.orthogonalProjection x : E) + ⟪u, x⟫_ℝ • u) ∈ (ℝ ∙ u)ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left, inner_add_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq, hun]
      have hp : ⟪(K.orthogonalProjection x : E), u⟫_ℝ = 0 :=
        hu _ (K.orthogonalProjection x).property
      rw [hp, real_inner_comm x u]
      ring

theorem orthogonalProjection_unit_extension_norm (K : Submodule ℝ E) {u : E}
    (hu : u ∈ Kᗮ) (hun : ‖u‖ = 1) (x : E) :
    ‖((K ⊔ ℝ ∙ u).orthogonalProjection x : E)‖ ^ 2 =
      ‖(K.orthogonalProjection x : E)‖ ^ 2 + ⟪u, x⟫_ℝ ^ 2 := by
  rw [orthogonalProjection_unit_extension K hu hun x, norm_add_sq_real,
    real_inner_smul_right, norm_smul, hun, mul_one, Real.norm_eq_abs, sq_abs]
  have hp : ⟪(K.orthogonalProjection x : E), u⟫_ℝ = 0 :=
    hu _ (K.orthogonalProjection x).property
  rw [hp]
  ring

/-- After a fixed initial subspace, one genuinely observation-dependent query chosen from a
countable palette increases posterior energy by exactly 1/d when it is unit and perpendicular. -/
theorem spherical_selected_unit_extension_energy [Nontrivial E] (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (u : ι → E)
    (hu : ∀ i, u i ∈ Kᗮ) (hun : ∀ i, ‖u i‖ = 1) (choice : E → ι)
    (hc : @Measurable E ι (projectionInformation K) inferInstance choice) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) |
        selectedProjectionInformation (fun i => K ⊔ ℝ ∙ u i) choice]) x‖ ^ 2 ∂sphericalLaw E) =
      ((Module.finrank ℝ K : ℝ) + 1) / (Module.finrank ℝ E : ℝ) := by
  let U : E → E := fun x => u (choice x)
  have hU : @Measurable E E (projectionInformation K) mE U :=
    (measurable_of_countable u).comp hc
  have hM := spherical_condExp_selected_extension K (fun i => K ⊔ ℝ ∙ u i)
    (fun _ => le_sup_left) choice hc
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hp : MemLp (fun x => (K.orthogonalProjection x : E)) 2 (sphericalLaw E) :=
    (K.subtypeL.comp K.orthogonalProjection).comp_memLp' hV
  have hpi : Integrable (fun x => ‖(K.orthogonalProjection x : E)‖ ^ 2) (sphericalLaw E) :=
    (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have hUi : MemLp (fun x => ⟪U x, x⟫_ℝ) 2 (sphericalLaw E) := by
    apply MemLp.of_bound
      ((continuous_fst.inner continuous_snd).measurable.comp
        ((hU.mono (projectionInformation_le K) le_rfl).prodMk measurable_id)).aestronglyMeasurable 1
    filter_upwards [sphericalLaw_unit (E := E)] with x hx
    have h := norm_inner_le_norm (𝕜 := ℝ) (U x) x
    simpa only [Function.comp_def, id_eq, U, hun, hx, one_mul] using h
  calc
    _ = ∫ x, ‖(K.orthogonalProjection x : E)‖ ^ 2 + ⟪U x, x⟫_ℝ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      filter_upwards [hM] with x hx
      rw [← hx]
      exact orthogonalProjection_unit_extension_norm K (hu (choice x)) (hun (choice x)) x
    _ = _ := by
      rw [integral_add hpi hUi.integrable_sq, spherical_projection_second_moment,
        spherical_adapted_unit_direction_second_moment K hr U hU
          (fun x => hu (choice x)) (fun x => hun (choice x))]
      ring

/-- The information available after the old projection and precisely one additional response. -/
def oneMoreLinearInformation (K : Submodule ℝ E) (U : E → E) : MeasurableSpace E :=
  projectionInformation K ⊔ MeasurableSpace.comap (fun x => ⟪U x, x⟫_ℝ) inferInstance

/-- The selected projection reveals exactly the old observations and the new scalar response. -/
theorem selected_unit_extension_information (K : Submodule ℝ E) (u : ι → E)
    (hu : ∀ i, u i ∈ Kᗮ) (hun : ∀ i, ‖u i‖ = 1) (choice : E → ι)
    (hc : @Measurable E ι (projectionInformation K) inferInstance choice) :
    selectedProjectionInformation (fun i => K ⊔ ℝ ∙ u i) choice =
      oneMoreLinearInformation K (fun x => u (choice x)) := by
  let L : ι → Submodule ℝ E := fun i => K ⊔ ℝ ∙ u i
  let U : E → E := fun x => u (choice x)
  let m := oneMoreLinearInformation K U
  letI : MeasurableSpace E := mE
  have he (x : E) : selectedProjection L choice x =
      (K.orthogonalProjection x : E) + ⟪U x, x⟫_ℝ • U x :=
    orthogonalProjection_unit_extension K (hu (choice x)) (hun (choice x)) x
  apply le_antisymm
  · have hcm : @Measurable E ι m inferInstance choice := hc.mono le_sup_left le_rfl
    have hUm : @Measurable E E m mE U := (measurable_of_countable u).comp hcm
    have hpm : @Measurable E E m mE (fun x => (K.orthogonalProjection x : E)) :=
      measurable_iff_comap_le.mpr le_sup_left
    have hrm : @Measurable E ℝ m inferInstance (fun x => ⟪U x, x⟫_ℝ) :=
      measurable_iff_comap_le.mpr le_sup_right
    have hsel : @Measurable E E m mE (selectedProjection L choice) := by
      have h := hpm.add (hrm.smul hUm)
      convert! h using 1
      exact funext he
    exact measurable_iff_comap_le.mp (hcm.prodMk hsel)
  · change projectionInformation K ⊔ MeasurableSpace.comap (fun x => ⟪U x, x⟫_ℝ) _ ≤ _
    have hpair : @Measurable E (ι × E) (selectedProjectionInformation L choice) inferInstance
        (fun x => (choice x, selectedProjection L choice x)) := measurable_iff_comap_le.mpr le_rfl
    have hUs : @Measurable E E (selectedProjectionInformation L choice) mE U :=
      (measurable_of_countable u).comp hpair.fst
    apply sup_le
    · have hproj : Measurable (fun x => (K.orthogonalProjection x : E)) :=
        (K.subtypeL.comp K.orthogonalProjection).continuous.measurable
      have h := hproj.comp hpair.snd
      have hfun : (fun x => (K.orthogonalProjection (selectedProjection L choice x) : E)) =
          (fun x => (K.orthogonalProjection x : E)) := by
        funext x
        exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_starProjection_of_le
          (le_sup_left : K ≤ L (choice x)) x)
      simp only [Function.comp_def, hfun] at h
      exact measurable_iff_comap_le.mp h
    · have h : @Measurable E ℝ (selectedProjectionInformation L choice) inferInstance
          (fun x => ⟪U x, selectedProjection L choice x⟫_ℝ) :=
        (continuous_fst.inner continuous_snd).measurable.comp (hUs.prodMk hpair.snd)
      have hfun : (fun x => ⟪U x, selectedProjection L choice x⟫_ℝ) =
          (fun x => ⟪U x, x⟫_ℝ) := by
        funext x
        have hmem : U x ∈ L (choice x) :=
          (show (ℝ ∙ U x) ≤ L (choice x) from le_sup_right)
            (Submodule.mem_span_singleton_self (U x))
        simpa only [Submodule.coe_inner, selectedProjection] using
          Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
            (⟨U x, hmem⟩ : L (choice x)) x
      change @Measurable E ℝ (selectedProjectionInformation L choice) inferInstance
        (fun x => ⟪U x, selectedProjection L choice x⟫_ℝ) at h
      rw [hfun] at h
      exact measurable_iff_comap_le.mp h

/-- A single counted adaptive response after a fixed initial observation space has the exact
posterior energy (dim K + 1)/d for a countable palette of perpendicular unit directions. -/
theorem spherical_one_more_query_energy [Nontrivial E] (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (u : ι → E)
    (hu : ∀ i, u i ∈ Kᗮ) (hun : ∀ i, ‖u i‖ = 1) (choice : E → ι)
    (hc : @Measurable E ι (projectionInformation K) inferInstance choice) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) |
        oneMoreLinearInformation K (fun x => u (choice x))]) x‖ ^ 2 ∂sphericalLaw E) =
      ((Module.finrank ℝ K : ℝ) + 1) / (Module.finrank ℝ E : ℝ) := by
  rw [← selected_unit_extension_information K u hu hun choice hc]
  exact spherical_selected_unit_extension_energy K hr u hu hun choice hc

end
end Nonsmooth
