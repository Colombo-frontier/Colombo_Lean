import Nonsmooth.SphereRisk
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Metric
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Normalized Lebesgue measure on the closed unit ball. -/
def euclideanBallLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure E :=
  (volume (closedBall (0 : E) 1))⁻¹ • (volume : Measure E).restrict (closedBall (0 : E) 1)

instance euclideanBallLaw_probability : IsProbabilityMeasure (euclideanBallLaw E) := by
  constructor
  rw [euclideanBallLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (measure_closedBall_pos (volume : Measure E) 0 (by norm_num)).ne'
    measure_closedBall_lt_top.ne

/-- Normalization sends zero to zero; that exceptional point has probability zero in positive
dimension. This convention commutes with every linear isometry. -/
def normalizedDirection (x : E) : E := ‖x‖⁻¹ • x

theorem normalizedDirection_measurable : Measurable (normalizedDirection (E := E)) :=
  measurable_id.norm.inv.smul measurable_id

theorem normalizedDirection_norm {x : E} (hx : x ≠ 0) : ‖normalizedDirection x‖ = 1 := by
  simp [normalizedDirection, norm_smul, hx]

theorem normalizedDirection_isometry (f : E ≃ₗᵢ[ℝ] E) (x : E) :
    f (normalizedDirection x) = normalizedDirection (f x) := by
  simp [normalizedDirection]

theorem euclideanBallLaw_isometry (f : E ≃ₗᵢ[ℝ] E) :
    (euclideanBallLaw E).map f = euclideanBallLaw E := by
  have hf : Measurable f := f.continuous.measurable
  have hpre : f ⁻¹' closedBall (0 : E) 1 = closedBall (0 : E) 1 := by
    ext x
    simp only [Set.mem_preimage, mem_closedBall, dist_zero_right, f.norm_map]
  have hr : ((volume : Measure E).restrict (closedBall (0 : E) 1)).map f =
      (volume : Measure E).restrict (closedBall (0 : E) 1) := by
    ext s hs
    rw [Measure.map_apply hf hs, Measure.restrict_apply (hf hs), Measure.restrict_apply hs]
    have he : f ⁻¹' (s ∩ closedBall (0 : E) 1) = f ⁻¹' s ∩ closedBall (0 : E) 1 := by
      rw [Set.preimage_inter, hpre]
    rw [← he, ← Measure.map_apply hf (hs.inter measurableSet_closedBall), f.measurePreserving.map_eq]
  rw [euclideanBallLaw, Measure.map_smul, hr]

/-- An actual rotationally invariant probability prior, obtained by radial projection of uniform
ball volume. Its support is the unit sphere in every positive dimension. -/
def sphericalLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure E :=
  (euclideanBallLaw E).map normalizedDirection

instance sphericalLaw_probability : IsProbabilityMeasure (sphericalLaw E) :=
  Measure.isProbabilityMeasure_map normalizedDirection_measurable.aemeasurable

theorem sphericalLaw_isometry (f : E ≃ₗᵢ[ℝ] E) :
    (sphericalLaw E).map f = sphericalLaw E := by
  rw [sphericalLaw, Measure.map_map f.continuous.measurable normalizedDirection_measurable]
  have he : (fun x => f (normalizedDirection x)) = fun x => normalizedDirection (f x) :=
    funext (normalizedDirection_isometry f)
  change (euclideanBallLaw E).map (fun x => f (normalizedDirection x)) = _
  rw [he]
  change (euclideanBallLaw E).map (normalizedDirection ∘ f) = _
  rw [← Measure.map_map normalizedDirection_measurable f.continuous.measurable,
    euclideanBallLaw_isometry]

theorem sphericalLaw_unit [Nontrivial E] : ∀ᵐ u ∂sphericalLaw E, ‖u‖ = 1 := by
  have hn : ∀ᵐ x ∂(volume : Measure E), x ≠ 0 := by
    simpa using (Set.countable_singleton (0 : E)).ae_notMem (volume : Measure E)
  have hb : ∀ᵐ x ∂euclideanBallLaw E, x ≠ 0 :=
    Measure.ae_smul_measure (ae_restrict_of_ae hn) _
  apply (ae_map_iff normalizedDirection_measurable.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  filter_upwards [hb] with x hx
  exact normalizedDirection_norm hx

theorem sphericalLaw_measurePreserving (f : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving f (sphericalLaw E) (sphericalLaw E) :=
  ⟨f.continuous.measurable, sphericalLaw_isometry f⟩

theorem sphericalLaw_coordinate_moment_equal {u v : E} (hn : ‖u‖ = ‖v‖) :
    (∫ x, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E) = ∫ x, ⟪v, x⟫_ℝ ^ 2 ∂sphericalLaw E := by
  let f : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (u - v))ᗮ.reflection
  have hfu : f u = v := Submodule.reflection_sub hn
  calc
    _ = ∫ x, ⟪v, f x⟫_ℝ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change ⟪u, x⟫_ℝ ^ 2 = ⟪v, f x⟫_ℝ ^ 2
      rw [← hfu, f.inner_map_map]
    _ = _ := (sphericalLaw_measurePreserving f).integral_comp
      f.toMeasurableEquiv.measurableEmbedding (fun x : E => ⟪v, x⟫_ℝ ^ 2)

theorem sphericalLaw_unit_second_moment [Nontrivial E] {u : E} (hu : ‖u‖ = 1) :
    (∫ x, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E) = 1 / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hb (i : Fin (Module.finrank ℝ E)) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x => ⟪b i, x⟫_ℝ ^ 2) (sphericalLaw E) :=
    (hV.const_inner (b i)).integrable_sq
  have he (i : Fin (Module.finrank ℝ E)) :
      (∫ x, ⟪b i, x⟫_ℝ ^ 2 ∂sphericalLaw E) = ∫ x, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E :=
    sphericalLaw_coordinate_moment_equal ((hb i).trans hu.symm)
  have hs (x : E) : (∑ i, ⟪b i, x⟫_ℝ ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right x
  have hsum : (Module.finrank ℝ E : ℝ) * (∫ x, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E) = 1 := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E), ∫ x, ⟪b i, x⟫_ℝ ^ 2 ∂sphericalLaw E := by
        simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x, ∑ i, ⟪b i, x⟫_ℝ ^ 2 ∂sphericalLaw E :=
        (integral_finsetSum _ (fun i _ => hi i)).symm
      _ = ∫ _ : E, (1 : ℝ) ∂sphericalLaw E := by
        apply integral_congr_ae
        filter_upwards [sphericalLaw_unit (E := E)] with x hx
        rw [hs, hx, one_pow]
      _ = 1 := by simp
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  apply (eq_div_iff hd.ne').mpr
  nlinarith

theorem sphericalLaw_second_moment [Nontrivial E] (u : E) :
    (∫ x, ⟪u, x⟫_ℝ ^ 2 ∂sphericalLaw E) = ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have he : ‖u‖ • normalizedDirection u = u := by simp [normalizedDirection, smul_smul, hn]
  calc
    _ = ∫ x, ‖u‖ ^ 2 * ⟪normalizedDirection u, x⟫_ℝ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change ⟪u, x⟫_ℝ ^ 2 = ‖u‖ ^ 2 * ⟪normalizedDirection u, x⟫_ℝ ^ 2
      conv_lhs => rw [← he, real_inner_smul_left, mul_pow]
    _ = _ := by
      rw [integral_const_mul, sphericalLaw_unit_second_moment (normalizedDirection_norm hu)]
      ring

theorem sphericalLaw_mean_zero : (∫ x : E, x ∂sphericalLaw E) = 0 := by
  let f : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have h := (sphericalLaw_measurePreserving f).integral_comp
    f.toMeasurableEquiv.measurableEmbedding (fun x : E => x)
  change (∫ x : E, -x ∂sphericalLaw E) = ∫ x : E, x ∂sphericalLaw E at h
  rw [integral_neg] at h
  have hz : (2 : ℝ) • (∫ x : E, x ∂sphericalLaw E) = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

abbrev UnitDirection (E : Type*) [NormedAddCommGroup E] := {u : E // ‖u‖ = 1}

/-- The same prior with its unit-norm support enforced by the parameter type. -/
def unitSphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure (UnitDirection E) :=
  (sphericalLaw E).comap Subtype.val

instance unitSphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (unitSphereLaw E) := by
  have he : MeasurableEmbedding (Subtype.val : UnitDirection E → E) :=
    MeasurableEmbedding.subtype_coe (isClosed_eq continuous_norm continuous_const).measurableSet
  apply he.isProbabilityMeasure_comap
  filter_upwards [sphericalLaw_unit (E := E)] with u hu
  exact ⟨⟨u, hu⟩, rfl⟩

theorem unitSphereLaw_integral [Nontrivial E] (f : E → ℝ) :
    (∫ u : UnitDirection E, f u.val ∂unitSphereLaw E) = ∫ x, f x ∂sphericalLaw E := by
  rw [unitSphereLaw]
  erw [integral_subtype_comap (μ := sphericalLaw E) (s := {u : E | ‖u‖ = 1})
    (isClosed_eq continuous_norm continuous_const).measurableSet f]
  have hres : (sphericalLaw E).restrict {u : E | ‖u‖ = 1} = sphericalLaw E :=
    Measure.restrict_eq_self_of_ae_mem (sphericalLaw_unit (E := E))
  erw [hres]

theorem unitSphereLaw_second_moment [Nontrivial E] (u : E) :
    (∫ v : UnitDirection E, ⟪u, v.val⟫_ℝ ^ 2 ∂unitSphereLaw E) =
      ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  exact (unitSphereLaw_integral (fun v => ⟪u, v⟫_ℝ ^ 2)).trans (sphericalLaw_second_moment u)

end
end Nonsmooth
