import Nonsmooth.CountableProtocol

open MeasureTheory Function
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def fallbackOrthogonal (K : Submodule ℝ E) : E :=
  if h : 0 < Module.finrank ℝ Kᗮ then
    ((stdOrthonormalBasis ℝ Kᗮ) ⟨0, h⟩ : E) else 0

def completionDirection (K : Submodule ℝ E) (v : E) : E := by
  classical
  exact if (Kᗮ.orthogonalProjectionOnto v : E) = 0 then fallbackOrthogonal K
    else normalizedDirection (Kᗮ.orthogonalProjectionOnto v : E)

theorem fallbackOrthogonal_mem (K : Submodule ℝ E) : fallbackOrthogonal K ∈ Kᗮ := by
  unfold fallbackOrthogonal
  split
  · exact Subtype.property _
  · exact Submodule.zero_mem _

theorem fallbackOrthogonal_norm (K : Submodule ℝ E) (hr : 0 < Module.finrank ℝ Kᗮ) :
    ‖fallbackOrthogonal K‖ = 1 := by
  unfold fallbackOrthogonal
  rw [dif_pos hr]
  exact (stdOrthonormalBasis ℝ Kᗮ).orthonormal.1 _

theorem completionDirection_mem (K : Submodule ℝ E) (v : E) : completionDirection K v ∈ Kᗮ := by
  unfold completionDirection
  split
  · exact fallbackOrthogonal_mem K
  · exact Kᗮ.smul_mem _ (Kᗮ.orthogonalProjectionOnto v).property

theorem completionDirection_norm (K : Submodule ℝ E) (hr : 0 < Module.finrank ℝ Kᗮ) (v : E) :
    ‖completionDirection K v‖ = 1 := by
  unfold completionDirection
  split
  · exact fallbackOrthogonal_norm K hr
  · rename_i h
    exact normalizedDirection_norm h

/-- Orthogonal completion preserves the original query, including a zero or redundant query. -/
theorem completionDirection_contains (K : Submodule ℝ E) (v : E) :
    v ∈ K ⊔ ℝ ∙ completionDirection K v := by
  let r : E := (Kᗮ.orthogonalProjectionOnto v : E)
  have hv : (K.orthogonalProjectionOnto v : E) + r = v :=
    by simpa only [Submodule.starProjection_apply] using K.starProjection_add_starProjection_orthogonal v
  suffices hm : r ∈ ℝ ∙ completionDirection K v by
    have hsum : (K.orthogonalProjectionOnto v : E) + r ∈ K ⊔ ℝ ∙ completionDirection K v :=
      Submodule.add_mem_sup (K.orthogonalProjectionOnto v).property hm
    simpa only [hv] using hsum
  by_cases hr : r = 0
  · rw [hr]
    exact Submodule.zero_mem _
  · have hc : completionDirection K v = normalizedDirection r := if_neg hr
    have he : ‖r‖ • normalizedDirection r = r := by
      simp [normalizedDirection, smul_smul, norm_ne_zero_iff.mpr hr]
    have hm : r ∈ ℝ ∙ completionDirection K v := by
      rw [hc]
      exact Submodule.mem_span_singleton.mpr ⟨‖r‖, he⟩
    exact hm

variable {ι κ : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

theorem selected_linear_response_measurable (K : ι → Submodule ℝ E) (choice : E → ι)
    (v : ι → E) (hv : ∀ i, v i ∈ K i) :
    @Measurable E ℝ (selectedProjectionInformation K choice) inferInstance
      (fun x => ⟪v (choice x), x⟫_ℝ) := by
  have hp : @Measurable E (ι × E) (selectedProjectionInformation K choice) inferInstance
      (fun x => (choice x, selectedProjection K choice x)) := measurable_iff_comap_le.mpr le_rfl
  have hV : @Measurable E E (selectedProjectionInformation K choice) mE (fun x => v (choice x)) :=
    (measurable_of_countable v).comp hp.fst
  have h : @Measurable E ℝ (selectedProjectionInformation K choice) inferInstance
      (fun x => ⟪v (choice x), selectedProjection K choice x⟫_ℝ) :=
    (continuous_fst.inner continuous_snd).measurable.comp (hV.prodMk hp.snd)
  have he : (fun x => ⟪v (choice x), selectedProjection K choice x⟫_ℝ) =
      (fun x => ⟪v (choice x), x⟫_ℝ) := by
    funext x
    simpa only [selectedProjection, Submodule.coe_inner] using
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
        ⟨v (choice x), hv (choice x)⟩ x)
  rwa [he] at h

/-- Coarsening the branch index and projecting onto a smaller space only loses information. -/
theorem selectedProjectionInformation_pullback (K : ι → Submodule ℝ E)
    (L : κ → Submodule ℝ E) (f : κ → ι) (hKL : ∀ j, K (f j) ≤ L j) (choice : E → κ) :
    selectedProjectionInformation K (fun x => f (choice x)) ≤ selectedProjectionInformation L choice := by
  have hp : @Measurable E (κ × E) (selectedProjectionInformation L choice) inferInstance
      (fun x => (choice x, selectedProjection L choice x)) := measurable_iff_comap_le.mpr le_rfl
  have hf : @Measurable E ι (selectedProjectionInformation L choice) inferInstance
      (fun x => f (choice x)) := by
    convert! (measurable_of_countable f).comp hp.fst using 1
  have hproj : Measurable (fun p : E × ι => ((K p.2).orthogonalProjectionOnto p.1 : E)) :=
    measurable_from_prod_countable_left (fun i =>
      ((K i).subtypeL.comp (K i).orthogonalProjectionOnto).continuous.measurable)
  have hm : @Measurable E E (selectedProjectionInformation L choice) mE
      (fun x => ((K (f (choice x))).orthogonalProjectionOnto (selectedProjection L choice x) : E)) :=
    by convert! hproj.comp (hp.snd.prodMk hf) using 1
  have he : (fun x => ((K (f (choice x))).orthogonalProjectionOnto (selectedProjection L choice x) : E)) =
      selectedProjection K (fun x => f (choice x)) := by
    funext x
    simpa only [selectedProjection, Submodule.starProjection_apply] using
      congrArg Subtype.val
        (Submodule.orthogonalProjectionOnto_starProjection_of_le (hKL (choice x)) x)
  rw [he] at hm
  apply measurable_iff_comap_le.mp
  convert! hf.prodMk hm using 1

end
end Nonsmooth
