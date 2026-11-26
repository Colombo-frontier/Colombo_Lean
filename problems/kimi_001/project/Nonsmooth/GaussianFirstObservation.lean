import Nonsmooth.ReflectionObservation
import Nonsmooth.GaussianInitialCovariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

theorem supportSingleObservation_congr_inner (u : E) {a b : Fin k → E}
    (h : ∀ i, ⟪a i, u⟫_ℝ = ⟪b i, u⟫_ℝ) :
    supportSingleObservation u a = supportSingleObservation u b := by
  have hv : finiteSupport a u = finiteSupport b u := by
    unfold finiteSupport
    simp_rw [h]
  have hw : supportWinner a u = supportWinner b u := by
    apply (supportWinner_eq_iff a u (supportWinner b u)).mpr
    constructor
    · rw [hv, h, supportWinner_attained]
    · intro j hj
      rw [h, hv]
      exact ((supportWinner_eq_iff b u (supportWinner b u)).mp rfl).2 j hj
  exact Prod.ext hw hv

theorem supportSingleObservation_reflection (K : Submodule ℝ E) {u : E} (hu : u ∈ K)
    (a : Fin k → E) :
    supportSingleObservation u (fun i => K.reflection (a i)) = supportSingleObservation u a := by
  apply supportSingleObservation_congr_inner
  intro i
  calc
    ⟪K.reflection (a i), u⟫_ℝ = ⟪K.reflection (a i), K.reflection u⟫_ℝ := by
      rw [K.reflection_mem_subspace_eq_self hu]
    _ = ⟪a i, u⟫_ℝ := K.reflection.inner_map_map (a i) u

theorem gaussianAmbientRows_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (fun a : Fin k → E => fun i => e (a i))
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) :=
  measurePreserving_pi _ _ (fun _ =>
    ⟨e.continuous.measurable, gaussianAmbientRowLaw_isometry e⟩)

theorem gaussian_single_observation_mean_projection [Nontrivial E]
    (K : Submodule ℝ E) {u : E} (hu : u ∈ K) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E),
      (K.orthogonalProjection
        (((Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[
          fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation u) inferInstance]) a) : E) =
      ((Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[
        fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation u) inferInstance]) a := by
  let e : (Fin k → E) ≃ᵐ (Fin k → E) :=
    MeasurableEquiv.piCongrRight (fun _ => K.reflection.toMeasurableEquiv)
  apply reflection_observation_condExp_projection _ e
    (gaussianAmbientRows_isometry K.reflection) _ (supportSingleObservation_measurable u)
    (supportSingleObservation_reflection K hu) _ gaussianAmbientRows_aggregate_integrable K
  intro a
  exact (map_sum K.reflection a Finset.univ).symm

/-- The first maximum observation has at most k/d mean energy for a unit query. The sharper
logarithmic bound needed for the full adaptive theorem is not claimed here. -/
theorem gaussian_single_observation_energy [Nontrivial E] {u : E} (hu : ‖u‖ = 1) :
    (∫ a : Fin k → E, ‖((Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[
        fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation u) inferInstance]) a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        (k : ℝ) / (Module.finrank ℝ E : ℝ) := by
  let e : (Fin k → E) ≃ᵐ (Fin k → E) :=
    MeasurableEquiv.piCongrRight (fun _ => (ℝ ∙ u).reflection.toMeasurableEquiv)
  have h := reflection_observation_condExp_energy _ e
    (gaussianAmbientRows_isometry (ℝ ∙ u).reflection) _ (supportSingleObservation_measurable u)
    (supportSingleObservation_reflection (ℝ ∙ u) (Submodule.mem_span_singleton_self u))
    _ gaussianAmbientRows_aggregate_memLp hu
    (fun a => (map_sum (ℝ ∙ u).reflection a Finset.univ).symm)
  apply h.trans
  simpa only [hu, one_pow, mul_one] using gaussianAmbientRows_inner_second_le (k := k) u

theorem exists_unit_direction_spanning [Nontrivial E] (q : E) :
    ∃ u : E, ‖u‖ = 1 ∧ q ∈ ℝ ∙ u := by
  by_cases hq : q = 0
  · let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
    refine ⟨stdOrthonormalBasis ℝ E i, (stdOrthonormalBasis ℝ E).orthonormal.1 i, ?_⟩
    rw [hq]
    exact Submodule.zero_mem _
  · refine ⟨‖q‖⁻¹ • q, ?_, ?_⟩
    · simp [norm_smul, Real.norm_eq_abs, norm_ne_zero_iff.mpr hq]
    · rw [Submodule.mem_span_singleton]
      refine ⟨‖q‖, ?_⟩
      simp [smul_smul, norm_ne_zero_iff.mpr hq]

theorem gaussian_single_observation_energy_arbitrary [Nontrivial E] (q : E) :
    (∫ a : Fin k → E, ‖((Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[
        fun a => ∑ i, a i | MeasurableSpace.comap (supportSingleObservation q) inferInstance]) a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        (k : ℝ) / (Module.finrank ℝ E : ℝ) := by
  obtain ⟨u, hu, hq⟩ := exists_unit_direction_spanning q
  let e : (Fin k → E) ≃ᵐ (Fin k → E) :=
    MeasurableEquiv.piCongrRight (fun _ => (ℝ ∙ u).reflection.toMeasurableEquiv)
  have h := reflection_observation_condExp_energy _ e
    (gaussianAmbientRows_isometry (ℝ ∙ u).reflection) _ (supportSingleObservation_measurable q)
    (supportSingleObservation_reflection (ℝ ∙ u) hq)
    _ gaussianAmbientRows_aggregate_memLp hu
    (fun a => (map_sum (ℝ ∙ u).reflection a Finset.univ).symm)
  apply h.trans
  simpa only [hu, one_pow, mul_one] using gaussianAmbientRows_inner_second_le (k := k) u

theorem supportTranscriptInformation_first {Ω S : Type}
    [MeasurableSpace Ω] [MeasurableSpace S] (p : Policy Ω S E) (ω : Ω) :
    supportTranscriptInformation (k := k) p ω 1 =
      MeasurableSpace.comap (supportSingleObservation (p.query 0 ω (p.initial ω))) inferInstance := by
  let q := p.query 0 ω (p.initial ω)
  let F : (Fin k × ℝ) → SupportHistory E k 1 := fun h => fun _ => (q, h)
  have hF : Measurable F := measurable_pi_lambda _ (fun _ => measurable_const.prodMk measurable_id)
  let G : SupportHistory E k 1 → (Fin k × ℝ) := fun h => (h 0).2
  have hG : Measurable G := (measurable_pi_apply 0).snd
  have he : (fun a : Fin k → E => supportAugmentedTranscript p a ω 1) =
      F ∘ supportSingleObservation q := by
    funext a i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [supportAugmentedTranscript, Policy.stateOnHistory, F, q, supportSingleObservation]
    exact Fin.snoc_last _ _
  have hg : G ∘ (fun a : Fin k → E => supportAugmentedTranscript p a ω 1) =
      supportSingleObservation q := by
    rw [he]
    rfl
  apply le_antisymm
  · change MeasurableSpace.comap _ _ ≤ _
    rw [he]
    exact measurable_iff_comap_le.mp (hF.comp (Measurable.of_comap_le le_rfl))
  · rw [← hg]
    exact measurable_iff_comap_le.mp (hG.comp (Measurable.of_comap_le le_rfl))

/-- For every measurable policy and seed, its actual first posterior mean increment is bounded
by k/d, including zero and arbitrarily large queries. -/
theorem gaussianSupportMean_first_energy [Nontrivial E] {Ω S : Type}
    [MeasurableSpace Ω] [MeasurableSpace S] (p : Policy Ω S E) (ω : Ω) :
    (∫ a : Fin k → E, ‖gaussianSupportMean p ω 1 a - gaussianSupportMean p ω 0 a‖ ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        (k : ℝ) / (Module.finrank ℝ E : ℝ) := by
  rw [gaussianSupportMean_initial]
  simp only [sub_zero]
  simp only [gaussianSupportMean, supportTranscriptInformation_first]
  exact gaussian_single_observation_energy_arbitrary (k := k) (p.query 0 ω (p.initial ω))

end
end Nonsmooth
