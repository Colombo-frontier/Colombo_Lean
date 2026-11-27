import Nonsmooth.ContinuousUpdate

open MeasureTheory Function
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem completionDirection_measurable (K : Submodule ℝ E) : Measurable (completionDirection K) := by
  classical
  have hp : Measurable (fun v => (Kᗮ.orthogonalProjectionOnto v : E)) :=
    (Kᗮ.subtypeL.comp Kᗮ.orthogonalProjectionOnto).continuous.measurable
  exact Measurable.ite (hp (measurableSet_singleton 0)) measurable_const
    (normalizedDirection_measurable.comp hp)

theorem linearIsometry_apply_sum (A : E ≃ₗᵢ[ℝ] E) (z : E) :
    A z = ∑ i : Fin (Module.finrank ℝ E),
      ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ • A (stdOrthonormalBasis ℝ E i) := by
  have h := congrArg A ((stdOrthonormalBasis ℝ E).sum_repr' z)
  simpa only [map_sum, map_smul] using h.symm

theorem measurable_variable_isometry {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → E ≃ₗᵢ[ℝ] E) (hA : ∀ v, Measurable (fun ω => A ω v))
    (z : Ω → E) (hz : Measurable z) : Measurable (fun ω => A ω (z ω)) := by
  have h : Measurable (fun ω => ∑ i : Fin (Module.finrank ℝ E),
      ⟪stdOrthonormalBasis ℝ E i, z ω⟫_ℝ • A ω (stdOrthonormalBasis ℝ E i)) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((continuous_const.inner continuous_id).measurable.comp hz).smul (hA _)
  simpa only [← linearIsometry_apply_sum] using h

theorem measurable_variable_isometry_symm {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → E ≃ₗᵢ[ℝ] E) (hA : ∀ v, Measurable (fun ω => A ω v))
    (z : Ω → E) (hz : Measurable z) : Measurable (fun ω => (A ω).symm (z ω)) := by
  let b := stdOrthonormalBasis ℝ E
  have he (ω : Ω) : (A ω).symm (z ω) =
      ∑ i : Fin (Module.finrank ℝ E), ⟪A ω (b i), z ω⟫_ℝ • b i := by
    have h := b.sum_repr' ((A ω).symm (z ω))
    have hinner (i : Fin (Module.finrank ℝ E)) :
        ⟪b i, (A ω).symm (z ω)⟫_ℝ = ⟪A ω (b i), z ω⟫_ℝ := by
      have hh := (A ω).inner_map_map (b i) ((A ω).symm (z ω))
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hh.symm
    simpa only [hinner] using h.symm
  simp only [he]
  apply Finset.measurable_sum
  intro i hi
  exact ((continuous_fst.inner continuous_snd).measurable.comp ((hA _).prodMk hz)).smul measurable_const

theorem perpendicularReflection_measurable (z : E) : Measurable (fun w : E => perpendicularReflection w z) := by
  have h : Measurable (fun w : E =>
      -(((2 : ℝ) * (⟪w, z⟫_ℝ / ‖w‖ ^ 2)) • w - z)) := by
    exact (((measurable_const.mul (((continuous_id.inner continuous_const).measurable).div
      (continuous_norm.measurable.pow_const 2))).smul measurable_id).sub measurable_const).neg
  simpa only [perpendicularReflection_formula] using h

theorem perpendicularReflection_fix (K : Submodule ℝ E) {w z : E}
    (hw : w ∈ Kᗮ) (hz : z ∈ K) : perpendicularReflection w z = z := by
  apply Submodule.reflection_mem_subspace_eq_self
  apply (Submodule.mem_orthogonal_singleton_iff_inner_left).mpr
  exact (Submodule.mem_orthogonal K w).mp hw z hz

theorem perpendicularReflection_align {u e : E} (hn : ‖u‖ = ‖e‖) :
    perpendicularReflection (u - e) u = e := Submodule.reflection_sub hn

theorem perpendicularReflection_align_back {u e : E} (hn : ‖u‖ = ‖e‖) :
    perpendicularReflection (u - e) e = u := by
  have h := congrArg (perpendicularReflection (u - e)) (perpendicularReflection_align hn)
  simpa only [perpendicularReflection, Submodule.reflection_reflection] using h.symm

theorem perpendicularReflection_align_inner {u e : E} (hn : ‖u‖ = ‖e‖) (x : E) :
    ⟪e, perpendicularReflection (u - e) x⟫_ℝ = ⟪u, x⟫_ℝ := by
  have h := (ℝ ∙ (u - e))ᗮ.reflection.inner_map_map u x
  have he := perpendicularReflection_align hn
  change (ℝ ∙ (u - e))ᗮ.reflection u = e at he
  rwa [he] at h

theorem fixed_extension_information (K : Submodule ℝ E) (e : E)
    (he : e ∈ Kᗮ) (hen : ‖e‖ = 1) :
    projectionInformation (K ⊔ ℝ ∙ e) = oneMoreLinearInformation K (fun _ => e) := by
  apply le_antisymm
  · have hm := updatedProjection_measurable K (fun _ => e) measurable_const
    have heq : updatedProjection K (fun _ => e) =
        (fun x => ((K ⊔ ℝ ∙ e).orthogonalProjectionOnto x : E)) := by
      funext x
      exact updatedProjection_eq K (fun _ => e) (fun _ => he) (fun _ => hen) x
    rw [heq] at hm
    exact measurable_iff_comap_le.mp hm
  · apply sup_le (projectionInformation_mono le_sup_left)
    have hp : @Measurable E E (projectionInformation (K ⊔ ℝ ∙ e)) mE
        (fun x => ((K ⊔ ℝ ∙ e).orthogonalProjectionOnto x : E)) := measurable_iff_comap_le.mpr le_rfl
    have h : @Measurable E ℝ (projectionInformation (K ⊔ ℝ ∙ e)) inferInstance
        (fun x => ⟪e, ((K ⊔ ℝ ∙ e).orthogonalProjectionOnto x : E)⟫_ℝ) :=
      (continuous_const.inner continuous_id).measurable.comp hp
    have hem : e ∈ K ⊔ ℝ ∙ e := (show (ℝ ∙ e) ≤ K ⊔ ℝ ∙ e from le_sup_right)
      (Submodule.mem_span_singleton_self e)
    have heq (x : E) : ⟪e, ((K ⊔ ℝ ∙ e).orthogonalProjectionOnto x : E)⟫_ℝ = ⟪e, x⟫_ℝ :=
      by simpa only [Submodule.coe_inner] using
        (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨e, hem⟩ x)
    simp only [heq] at h
    exact measurable_iff_comap_le.mp h

/-- A history-dependent Householder map sends precisely the old observations and one new
response to a fixed enlarged observation subspace. -/
theorem alignment_information (K : Submodule ℝ E) (U : E → E)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) (e : E)
    (he : e ∈ Kᗮ) (hen : ‖e‖ = 1) :
    MeasurableSpace.comap (fun x => perpendicularReflection (U x - e) x)
      (projectionInformation (mE := mE) (K ⊔ ℝ ∙ e)) = oneMoreLinearInformation K U := by
  rw [fixed_extension_information K e he hen, oneMoreLinearInformation_eq_comap,
    MeasurableSpace.comap_comp, oneMoreLinearInformation_eq_comap]
  congr 1
  funext x
  apply Prod.ext
  · exact congrArg Subtype.val (projection_reflection_perpendicular K (Kᗮ.sub_mem (hUp x) he) x)
  · exact perpendicularReflection_align_inner ((hUn x).trans hen.symm) x

theorem variable_query_response_measurable (K : Submodule ℝ E) (U q : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hq : @Measurable E E (projectionInformation K) mE q)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1)
    (hqm : ∀ x, q x ∈ K ⊔ ℝ ∙ U x) :
    @Measurable E ℝ (oneMoreLinearInformation K U) inferInstance (fun x => ⟪q x, x⟫_ℝ) := by
  have hq' := hq.mono (show projectionInformation K ≤ oneMoreLinearInformation K U from le_sup_left) le_rfl
  have h : @Measurable E ℝ (oneMoreLinearInformation K U) inferInstance
      (fun x => ⟪q x, updatedProjection K U x⟫_ℝ) := (continuous_fst.inner continuous_snd).measurable.comp
    (hq'.prodMk (updatedProjection_measurable K U hU))
  have heq (x : E) : ⟪q x, updatedProjection K U x⟫_ℝ = ⟪q x, x⟫_ℝ := by
    rw [updatedProjection_eq K U hUp hUn]
    simpa only [Submodule.coe_inner] using
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨q x, hqm x⟩ x)
  simpa only [Function.comp_def, heq] using h

end
end Nonsmooth
