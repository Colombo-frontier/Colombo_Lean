import Nonsmooth.GaussianLinearTail
import Nonsmooth.ProductPosteriorAtoms
import Nonsmooth.SupportNoInformation

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_unit_inner_law {u : E} (hu : ‖u‖ = 1) :
    (euclideanGaussianLaw E).map (fun z : E => ⟪u, z⟫_ℝ) = gaussianReal 0 1 := by
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let v : E := stdOrthonormalBasis ℝ E i
  let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (u - v))ᗮ.reflection
  have he : e u = v := Submodule.reflection_sub
    (hu.trans ((stdOrthonormalBasis ℝ E).orthonormal.1 i).symm)
  have hfun : (fun z : E => ⟪u, z⟫_ℝ) = (fun z : E => ⟪v, z⟫_ℝ) ∘ e := by
    funext z
    change ⟪u, z⟫_ℝ = ⟪v, e z⟫_ℝ
    rw [← he, e.inner_map_map]
  have hv : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  rw [hfun, ← Measure.map_map hv e.continuous.measurable,
    euclideanGaussianLaw_isometry]
  exact euclideanGaussianLaw_coordinate i

theorem euclideanGaussian_hyperplane_zero {u : E} (hu : u ≠ 0) (y : ℝ) :
    euclideanGaussianLaw E {z : E | ⟪u, z⟫_ℝ = y} = 0 := by
  have hreal : gaussianReal 0 1 {y / ‖u‖} = 0 :=
    gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0) (measure_singleton _)
  have hunit : euclideanGaussianLaw E {z : E | ⟪normalizedDirection u, z⟫_ℝ = y / ‖u‖} = 0 := by
    have h := congrArg (fun μ : Measure ℝ => μ {y / ‖u‖})
      (euclideanGaussian_unit_inner_law (normalizedDirection_norm hu))
    try dsimp only at h
    have hm : Measurable (fun z : E => ⟪normalizedDirection u, z⟫_ℝ) :=
      (continuous_const.inner continuous_id).measurable
    rw [Measure.map_apply hm (measurableSet_singleton _), hreal] at h
    exact h
  apply measure_mono_null ?_ hunit
  intro z hz
  change ⟪u, z⟫_ℝ = y at hz
  simp only [mem_setOf_eq, normalizedDirection, real_inner_smul_left, hz, div_eq_inv_mul]

theorem truncatedGaussian_hyperplane_zero {u : E} (hu : u ≠ 0) (y : ℝ) :
    truncatedGaussianLaw E {z : E | ⟪u, z⟫_ℝ = y} = 0 := by
  rw [truncatedGaussianLaw_apply, measure_mono_null inter_subset_right (euclideanGaussian_hyperplane_zero hu y), mul_zero]

theorem gaussianAmbientRow_hyperplane_zero {u : E} (hu : u ≠ 0) (y : ℝ) :
    gaussianAmbientRowLaw E {a : E | ⟪a, u⟫_ℝ = y} = 0 := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  let c : ℝ := (Real.sqrt (Module.finrank ℝ E))⁻¹
  have hc : c ≠ 0 := (inv_pos.mpr (Real.sqrt_pos.mpr hd)).ne'
  have hm : Measurable (fun z : E => c • z) := measurable_const.smul measurable_id
  have hs : MeasurableSet {a : E | ⟪a, u⟫_ℝ = y} :=
    measurableSet_eq_fun (continuous_id.inner continuous_const).measurable measurable_const
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map, Measure.map_apply hm hs]
  have he : (fun z : E => c • z) ⁻¹' {a : E | ⟪a, u⟫_ℝ = y} =
      {z : E | ⟪c • u, z⟫_ℝ = y} := by
    ext z
    simp only [mem_preimage, mem_setOf_eq, real_inner_smul_left, real_inner_comm u, inner_smul_right]
  rw [he]
  exact truncatedGaussian_hyperplane_zero (smul_ne_zero hc hu) y

theorem gaussianAmbientRows_coordinate_hyperplane_zero {k : ℕ} (i : Fin k)
    {u : E} (hu : u ≠ 0) (y : ℝ) :
    Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E) {a : Fin k → E | ⟪a i, u⟫_ℝ = y} = 0 := by
  have hs : MeasurableSet {a : E | ⟪a, u⟫_ℝ = y} :=
    measurableSet_eq_fun (continuous_id.inner continuous_const).measurable measurable_const
  have h := congrArg (fun μ : Measure E => μ {a : E | ⟪a, u⟫_ℝ = y})
    (finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq
  try dsimp only at h
  rw [Measure.map_apply (measurable_pi_apply i) hs, gaussianAmbientRow_hyperplane_zero hu y] at h
  exact h

/-- Under the actual Gaussian prior, any fixed transcript containing a nonzero query has zero mass. -/
theorem gaussianSupportTranscript_atom_zero {k : ℕ} [Nonempty (Fin k)]
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (h : SupportHistory E k n) (j : Fin n) (hq : (h j).1 ≠ 0) :
    (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)).map
      (fun a => supportAugmentedTranscript p a ω n) {h} = 0 := by
  have hF : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp (measurable_id.prodMk measurable_const)
  rw [Measure.map_apply hF (measurableSet_singleton h)]
  apply measure_mono_null ?_ (gaussianAmbientRows_coordinate_hyperplane_zero (h j).2.1 hq (h j).2.2)
  intro a ha
  change supportAugmentedTranscript p a ω n = h at ha
  have ho := supportAugmentedTranscript_observations p a ω n j
  rw [ha] at ho
  change ⟪a (h j).2.1, (h j).1⟫_ℝ = (h j).2.2
  rw [ho.1, ← supportWinner_attained, ho.2]

theorem gaussianSupportTranscript_naive_conditioning_zero {k : ℕ} [Nonempty (Fin k)]
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (h : SupportHistory E k n) (j : Fin n) (hq : (h j).1 ≠ 0) :
    (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[|{a | supportAugmentedTranscript p a ω n = h}] = 0 := by
  have hF : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp (measurable_id.prodMk measurable_const)
  have hz := gaussianSupportTranscript_atom_zero p hp ω n h j hq
  rw [Measure.map_apply hF (measurableSet_singleton h)] at hz
  have hr : (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)).restrict
      {a | supportAugmentedTranscript p a ω n = h} = 0 := Measure.restrict_eq_zero.mpr hz
  simp only [ProbabilityTheory.cond, hr, smul_zero]

/-- The actual Markov posterior cannot equal naive event conditioning on a nonzero-query history. -/
theorem gaussianSupportPosterior_ne_naive_conditioning {k : ℕ} [Nonempty (Fin k)]
    {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (h : SupportHistory E k n) (j : Fin n) (hq : (h j).1 ≠ 0) :
    supportPosteriorKernel (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) p ω n h ≠
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E))[|{a | supportAugmentedTranscript p a ω n = h}] := by
  rw [gaussianSupportTranscript_naive_conditioning_zero p hp ω n h j hq]
  exact IsProbabilityMeasure.ne_zero _

theorem independent_support_response_cdf {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) (y : ℝ) :
    Measure.pi μ {a : Fin k → E | finiteSupport a u ≤ y} = ∏ i, μ i {z : E | ⟪z, u⟫_ℝ ≤ y} := by
  have he : {a : Fin k → E | finiteSupport a u ≤ y} =
      Set.univ.pi (fun _ : Fin k => {z : E | ⟪z, u⟫_ℝ ≤ y}) := by
    ext a
    simp only [mem_setOf_eq, finiteSupport, Finset.sup'_le_iff, Finset.mem_univ,
      forall_const, Set.mem_pi, Set.mem_univ]
  rw [he, Measure.pi_pi]

theorem gaussianAmbientRows_response_cdf {k : ℕ} [Nonempty (Fin k)] (u : E) (y : ℝ) :
    Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E) {a : Fin k → E | finiteSupport a u ≤ y} =
      (gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ y}) ^ k := by
  rw [independent_support_response_cdf]
  simp

theorem gaussianAmbientRows_response_atom_zero {k : ℕ} [Nonempty (Fin k)]
    {u : E} (hu : u ≠ 0) (y : ℝ) :
    Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E) {a : Fin k → E | finiteSupport a u = y} = 0 := by
  have hz : Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
      (⋃ i : Fin k, {a : Fin k → E | ⟪a i, u⟫_ℝ = y}) = 0 :=
    measure_iUnion_null_iff.mpr (fun i => gaussianAmbientRows_coordinate_hyperplane_zero i hu y)
  apply measure_mono_null ?_ hz
  intro a ha
  obtain ⟨i, hi⟩ := finiteSupport_attained a u
  exact mem_iUnion.mpr ⟨i, hi.symm.trans ha⟩

end
end Nonsmooth
