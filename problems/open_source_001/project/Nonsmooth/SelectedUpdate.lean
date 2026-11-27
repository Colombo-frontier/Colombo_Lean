import Nonsmooth.SelectedProjection

open MeasureTheory Function
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
variable {ι κ : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

theorem selectedProjection_square_integrable (K : ι → Submodule ℝ E)
    {choice : E → ι} (hc : Measurable choice) :
    Integrable (fun x => ‖selectedProjection K choice x‖ ^ 2) (sphericalLaw E) := by
  have hp : MemLp (selectedProjection K choice) 2 (sphericalLaw E) := by
    apply MemLp.of_bound (selectedProjection_measurable K hc).aestronglyMeasurable 1
    filter_upwards [sphericalLaw_unit (E := E)] with x hx
    have h := ((K (choice x)).orthogonalProjection.le_opNorm x)
    rw [hx, mul_one] at h
    exact h.trans (Submodule.orthogonalProjection_norm_le _)
  exact (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp

theorem selected_query_cell_measurable (K : ι → Submodule ℝ E) (choice : E → ι)
    (hbranch : ∀ i, MeasurableSet[projectionInformation (K i)] {x | choice x = i})
    (next : E → κ)
    (hn : @Measurable E κ (selectedProjectionInformation K choice) inferInstance next)
    (i : ι) (j : κ) :
    MeasurableSet[projectionInformation (K i)] {x | choice x = i ∧ next x = j} := by
  have h := selectedProjection_event_piece K choice hbranch (hn (measurableSet_singleton j)) i
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_comm]

/-- Exact expected gain from an additional unit perpendicular query, when the old observed
space and the new query are selected through countably many observable branches. -/
theorem spherical_selected_query_second_moment (K : ι → Submodule ℝ E)
    (choice : E → ι) (hc : Measurable choice)
    (hbranch : ∀ i, MeasurableSet[projectionInformation (K i)] {x | choice x = i})
    (next : E → κ)
    (hn : @Measurable E κ (selectedProjectionInformation K choice) inferInstance next)
    (u : ι → κ → E) (hu : ∀ i j, u i j ∈ (K i)ᗮ) (hun : ∀ i j, ‖u i j‖ = 1)
    (r : ℕ) (hr : 0 < r) (hdim : ∀ i, Module.finrank ℝ (K i)ᗮ = r) :
    (∫ x, ⟪u (choice x) (next x), x⟫_ℝ ^ 2 ∂sphericalLaw E) =
      (1 - ∫ x, ‖selectedProjection K choice x‖ ^ 2 ∂sphericalLaw E) / (r : ℝ) := by
  let U : E → E := fun x => u (choice x) (next x)
  let delta : E → ℝ := fun x => (1 - ‖selectedProjection K choice x‖ ^ 2) / (r : ℝ)
  let cells : ι × κ → Set E := fun p => {x | choice x = p.1 ∧ next x = p.2}
  have hcm (p : ι × κ) : MeasurableSet (cells p) :=
    projectionInformation_le (K p.1) _ (selected_query_cell_measurable K choice hbranch next hn p.1 p.2)
  have hdis : Pairwise (Disjoint on cells) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro x hxp hxq
    exact hpq (Prod.ext (hxp.1.symm.trans hxq.1) (hxp.2.symm.trans hxq.2))
  have hcover : (⋃ p, cells p) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨(choice x, next x), rfl, rfl⟩
  have hna : Measurable next := hn.mono (selectedProjectionInformation_le K hc) le_rfl
  have hUm : Measurable U := (measurable_of_countable (fun p : ι × κ => u p.1 p.2)).comp (hc.prodMk hna)
  have hUi : MemLp (fun x => ⟪U x, x⟫_ℝ) 2 (sphericalLaw E) := by
    apply MemLp.of_bound
      ((continuous_fst.inner continuous_snd).measurable.comp (hUm.prodMk measurable_id)).aestronglyMeasurable 1
    filter_upwards [sphericalLaw_unit (E := E)] with x hx
    have h := norm_inner_le_norm (𝕜 := ℝ) (U x) x
    simpa only [U, hun, hx, one_mul, Function.comp_apply, id_eq] using h
  have hdi : Integrable delta (sphericalLaw E) :=
    ((integrable_const (1 : ℝ)).sub (selectedProjection_square_integrable K hc)).div_const _
  have he : (∫ x, ⟪U x, x⟫_ℝ ^ 2 ∂sphericalLaw E) = ∫ x, delta x ∂sphericalLaw E := by
    conv_lhs => rw [← setIntegral_univ, ← hcover]
    conv_rhs => rw [← setIntegral_univ, ← hcover]
    rw [integral_iUnion hcm hdis hUi.integrable_sq.integrableOn,
      integral_iUnion hcm hdis hdi.integrableOn]
    apply tsum_congr
    intro p
    calc
      _ = ∫ x in cells p, ⟪u p.1 p.2, x⟫_ℝ ^ 2 ∂sphericalLaw E := by
        apply setIntegral_congr_fun (hcm p)
        intro x hx
        simp only [U, hx.1, hx.2]
      _ = (∫ x in cells p, (1 - ‖((K p.1).orthogonalProjection x : E)‖ ^ 2)
          ∂sphericalLaw E) / (r : ℝ) := by
        have h := spherical_perpendicular_event_second_moment (K p.1)
          (by simpa only [hdim] using hr) (hu p.1 p.2) (hun p.1 p.2)
          (selected_query_cell_measurable K choice hbranch next hn p.1 p.2)
        simpa only [hdim] using h
      _ = ∫ x in cells p, delta x ∂sphericalLaw E := by
        rw [← integral_div]
        apply setIntegral_congr_fun (hcm p)
        intro x hx
        have hp : selectedProjection K choice x = ((K p.1).orthogonalProjection x : E) :=
          congrArg (fun i => ((K i).orthogonalProjection x : E)) hx.1
        dsimp only [delta]
        rw [hp]
  rw [he, integral_div, integral_sub (integrable_const _) (selectedProjection_square_integrable K hc),
    integral_const]
  simp

theorem selected_refinement_branch (K : ι → Submodule ℝ E) (choice : E → ι)
    (hbranch : ∀ i, MeasurableSet[projectionInformation (K i)] {x | choice x = i})
    (next : E → κ)
    (hn : @Measurable E κ (selectedProjectionInformation K choice) inferInstance next)
    (u : ι → κ → E) (p : ι × κ) :
    MeasurableSet[projectionInformation (K p.1 ⊔ ℝ ∙ u p.1 p.2)]
      {x | (choice x, next x) = p} := by
  have h := projectionInformation_mono (le_sup_left : K p.1 ≤ K p.1 ⊔ ℝ ∙ u p.1 p.2) _
    (selected_query_cell_measurable K choice hbranch next hn p.1 p.2)
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Prod.ext_iff]

theorem selected_query_square_integrable (choice : E → ι) (hc : Measurable choice)
    (next : E → κ) (hn : Measurable next) (u : ι → κ → E) (hun : ∀ i j, ‖u i j‖ = 1) :
    Integrable (fun x => ⟪u (choice x) (next x), x⟫_ℝ ^ 2) (sphericalLaw E) := by
  have hUm : Measurable (fun x => u (choice x) (next x)) :=
    (measurable_of_countable (fun p : ι × κ => u p.1 p.2)).comp (hc.prodMk hn)
  have hUi : MemLp (fun x => ⟪u (choice x) (next x), x⟫_ℝ) 2 (sphericalLaw E) := by
    apply MemLp.of_bound
      ((continuous_fst.inner continuous_snd).measurable.comp (hUm.prodMk measurable_id)).aestronglyMeasurable 1
    filter_upwards [sphericalLaw_unit (E := E)] with x hx
    have h := norm_inner_le_norm (𝕜 := ℝ) (u (choice x) (next x)) x
    simpa only [hun, hx, one_mul, Function.comp_apply, id_eq] using h
  exact hUi.integrable_sq

/-- The posterior-energy update remains valid when the old observed subspace itself varies
between countably many history branches. Both old and new means are actual conditional expectations. -/
theorem spherical_selected_posterior_energy_update (K : ι → Submodule ℝ E)
    (choice : E → ι) (hc : Measurable choice)
    (hbranch : ∀ i, MeasurableSet[projectionInformation (K i)] {x | choice x = i})
    (next : E → κ)
    (hn : @Measurable E κ (selectedProjectionInformation K choice) inferInstance next)
    (u : ι → κ → E) (hu : ∀ i j, u i j ∈ (K i)ᗮ) (hun : ∀ i j, ‖u i j‖ = 1)
    (r : ℕ) (hr : 0 < r) (hdim : ∀ i, Module.finrank ℝ (K i)ᗮ = r) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) |
      selectedProjectionInformation (fun p : ι × κ => K p.1 ⊔ ℝ ∙ u p.1 p.2)
        (fun x => (choice x, next x))]) x‖ ^ 2 ∂sphericalLaw E) =
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | selectedProjectionInformation K choice]) x‖ ^ 2
      ∂sphericalLaw E) +
    (1 - ∫ x, ‖((sphericalLaw E)[(fun x : E => x) | selectedProjectionInformation K choice]) x‖ ^ 2
      ∂sphericalLaw E) / (r : ℝ) := by
  have hna : Measurable next := hn.mono (selectedProjectionInformation_le K hc) le_rfl
  have hold := spherical_condExp_selectedProjection K hc hbranch
  have hnew := spherical_condExp_selectedProjection
    (fun p : ι × κ => K p.1 ⊔ ℝ ∙ u p.1 p.2) (hc.prodMk hna)
    (selected_refinement_branch K choice hbranch next hn u)
  have heold : (∫ x, ‖((sphericalLaw E)[(fun x : E => x) |
      selectedProjectionInformation K choice]) x‖ ^ 2 ∂sphericalLaw E) =
      ∫ x, ‖selectedProjection K choice x‖ ^ 2 ∂sphericalLaw E := by
    apply integral_congr_ae
    filter_upwards [hold] with x hx
    rw [← hx]
  rw [heold]
  calc
    _ = ∫ x, ‖selectedProjection K choice x‖ ^ 2 +
        ⟪u (choice x) (next x), x⟫_ℝ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      filter_upwards [hnew] with x hx
      rw [← hx]
      exact orthogonalProjection_unit_extension_norm (K (choice x))
        (hu (choice x) (next x)) (hun (choice x) (next x)) x
    _ = _ := by
      rw [integral_add (selectedProjection_square_integrable K hc)
        (selected_query_square_integrable choice hc next hna u hun),
        spherical_selected_query_second_moment K choice hc hbranch next hn u hu hun r hr hdim]

/-- Even for an already adaptive subspace, its refinement adds precisely one scalar response. -/
theorem selected_refinement_information (K : ι → Submodule ℝ E) (choice : E → ι)
    (next : E → κ)
    (hn : @Measurable E κ (selectedProjectionInformation K choice) inferInstance next)
    (u : ι → κ → E) (hu : ∀ i j, u i j ∈ (K i)ᗮ) (hun : ∀ i j, ‖u i j‖ = 1) :
    selectedProjectionInformation (fun p : ι × κ => K p.1 ⊔ ℝ ∙ u p.1 p.2)
        (fun x => (choice x, next x)) =
      selectedProjectionInformation K choice ⊔
        MeasurableSpace.comap (fun x => ⟪u (choice x) (next x), x⟫_ℝ) inferInstance := by
  let L : ι × κ → Submodule ℝ E := fun p => K p.1 ⊔ ℝ ∙ u p.1 p.2
  let pair : E → ι × κ := fun x => (choice x, next x)
  let U : E → E := fun x => u (choice x) (next x)
  let newInfo := selectedProjectionInformation L pair
  let obsInfo := selectedProjectionInformation (mE := mE) K choice ⊔
    MeasurableSpace.comap (fun x => ⟪U x, x⟫_ℝ) inferInstance
  letI : MeasurableSpace E := mE
  have he (x : E) : selectedProjection L pair x =
      selectedProjection K choice x + ⟪U x, x⟫_ℝ • U x :=
    orthogonalProjection_unit_extension (K (choice x)) (hu (choice x) (next x)) (hun (choice x) (next x)) x
  have hold : @Measurable E (ι × E) (selectedProjectionInformation K choice) inferInstance
      (fun x => (choice x, selectedProjection K choice x)) := measurable_iff_comap_le.mpr le_rfl
  apply le_antisymm
  · have hcm : @Measurable E ι obsInfo inferInstance choice := hold.fst.mono le_sup_left le_rfl
    have hnm : @Measurable E κ obsInfo inferInstance next := hn.mono le_sup_left le_rfl
    have hum : @Measurable E E obsInfo mE U :=
      (measurable_of_countable (fun p : ι × κ => u p.1 p.2)).comp (hcm.prodMk hnm)
    have hpm : @Measurable E E obsInfo mE (selectedProjection K choice) :=
      hold.snd.mono le_sup_left le_rfl
    have hrm : @Measurable E ℝ obsInfo inferInstance (fun x => ⟪U x, x⟫_ℝ) :=
      measurable_iff_comap_le.mpr le_sup_right
    have hsel : @Measurable E E obsInfo mE (selectedProjection L pair) := by
      convert! hpm.add (hrm.smul hum) using 1
      exact funext he
    exact measurable_iff_comap_le.mp ((hcm.prodMk hnm).prodMk hsel)
  · have hnew : @Measurable E ((ι × κ) × E) newInfo inferInstance
        (fun x => (pair x, selectedProjection L pair x)) := measurable_iff_comap_le.mpr le_rfl
    have hum : @Measurable E E newInfo mE U :=
      (measurable_of_countable (fun p : ι × κ => u p.1 p.2)).comp hnew.fst
    apply sup_le
    · have hproj : Measurable (fun p : E × ι => ((K p.2).orthogonalProjection p.1 : E)) :=
        measurable_from_prod_countable_left (fun i =>
          ((K i).subtypeL.comp (K i).orthogonalProjection).continuous.measurable)
      have hpm : @Measurable E E newInfo mE
          (fun x => ((K (choice x)).orthogonalProjection (selectedProjection L pair x) : E)) :=
        by
        convert! hproj.comp (hnew.snd.prodMk hnew.fst.fst) using 1
      have hfun : (fun x => ((K (choice x)).orthogonalProjection (selectedProjection L pair x) : E)) =
          selectedProjection K choice := by
        funext x
        exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_starProjection_of_le
          (le_sup_left : K (choice x) ≤ L (pair x)) x)
      rw [hfun] at hpm
      exact measurable_iff_comap_le.mp (hnew.fst.fst.prodMk hpm)
    · have h : @Measurable E ℝ newInfo inferInstance
          (fun x => ⟪U x, selectedProjection L pair x⟫_ℝ) :=
        (continuous_fst.inner continuous_snd).measurable.comp (hum.prodMk hnew.snd)
      have hfun : (fun x => ⟪U x, selectedProjection L pair x⟫_ℝ) = (fun x => ⟪U x, x⟫_ℝ) := by
        funext x
        have hmem : U x ∈ L (pair x) :=
          (show (ℝ ∙ U x) ≤ L (pair x) from le_sup_right)
            (Submodule.mem_span_singleton_self (U x))
        simpa only [Submodule.coe_inner, selectedProjection] using
          Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
            (⟨U x, hmem⟩ : L (pair x)) x
      rw [hfun] at h
      exact measurable_iff_comap_le.mp h

end
end Nonsmooth
