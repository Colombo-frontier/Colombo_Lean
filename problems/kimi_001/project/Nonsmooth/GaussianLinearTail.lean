import Nonsmooth.GaussianSpectral

open MeasureTheory ProbabilityTheory Function Filter
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_inner_square_integrable (u : E) :
    Integrable (fun z : E => ⟪u, z⟫_ℝ ^ 2) (euclideanGaussianLaw E) := by
  have hV : MemLp (fun z : E => z) 2 (euclideanGaussianLaw E) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      euclideanGaussian_norm_square_integrable
  exact (hV.const_inner u).integrable_sq

theorem euclideanGaussian_unit_inner_second_moment {u : E} (hu : ‖u‖ = 1) :
    (∫ z : E, ⟪u, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) = 1 := by
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let v : E := stdOrthonormalBasis ℝ E i
  let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (u - v))ᗮ.reflection
  have he : e u = v := Submodule.reflection_sub (hu.trans ((stdOrthonormalBasis ℝ E).orthonormal.1 i).symm)
  have hp : MeasurePreserving e (euclideanGaussianLaw E) (euclideanGaussianLaw E) :=
    ⟨e.continuous.measurable, euclideanGaussianLaw_isometry e⟩
  calc
    _ = ∫ z : E, ⟪v, e z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      change ⟪u, z⟫_ℝ ^ 2 = ⟪v, e z⟫_ℝ ^ 2
      rw [← he, e.inner_map_map]
    _ = ∫ z : E, ⟪v, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E :=
      hp.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun z : E => ⟪v, z⟫_ℝ ^ 2)
    _ = 1 := euclideanGaussian_coordinate_second_moment i

theorem euclideanGaussian_inner_second_moment (u : E) :
    (∫ z : E, ⟪u, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) = ‖u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have he : ‖u‖ • normalizedDirection u = u := by simp [normalizedDirection, smul_smul, hn]
  calc
    _ = ∫ z : E, ‖u‖ ^ 2 * ⟪normalizedDirection u, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      change ⟪u, z⟫_ℝ ^ 2 = ‖u‖ ^ 2 * ⟪normalizedDirection u, z⟫_ℝ ^ 2
      conv_lhs => rw [← he, real_inner_smul_left, mul_pow]
    _ = _ := by
      rw [integral_const_mul, euclideanGaussian_unit_inner_second_moment (normalizedDirection_norm hu), mul_one]

theorem euclideanGaussian_inner_lower_tail (u : E) {t : ℝ} (ht : 0 < t) :
    (euclideanGaussianLaw E).real {z : E | ⟪u, z⟫_ℝ < -t} ≤ ‖u‖ ^ 2 / (2 * t ^ 2) := by
  let L : Set E := {z | ⟪u, z⟫_ℝ < -t}
  let R : Set E := {z | t < ⟪u, z⟫_ℝ}
  have hL : MeasurableSet L := measurableSet_lt (continuous_const.inner continuous_id).measurable measurable_const
  have hR : MeasurableSet R := measurableSet_lt measurable_const (continuous_const.inner continuous_id).measurable
  have hneg := congrArg (fun μ : Measure E => μ.real L)
    (euclideanGaussianLaw_isometry (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E))
  try dsimp only at hneg
  rw [map_measureReal_apply (LinearIsometryEquiv.neg ℝ).continuous.measurable hL] at hneg
  have he : (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) ⁻¹' L = R := by
    ext z
    change (⟪u, -z⟫_ℝ < -t) ↔ t < ⟪u, z⟫_ℝ
    rw [inner_neg_right, neg_lt_neg_iff]
  rw [he] at hneg
  have hd : Disjoint L R := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    change ⟪u, z⟫_ℝ < -t at hz
    change t < ⟪u, z⟫_ℝ at hz'
    linarith
  have hsub : L ∪ R ⊆ {z : E | t ^ 2 ≤ ⟪u, z⟫_ℝ ^ 2} := by
    intro z hz
    rcases hz with hz | hz
    · change ⟪u, z⟫_ℝ < -t at hz
      change t ^ 2 ≤ ⟪u, z⟫_ℝ ^ 2
      nlinarith
    · change t < ⟪u, z⟫_ℝ at hz
      change t ^ 2 ≤ ⟪u, z⟫_ℝ ^ 2
      nlinarith
  have hmass := measureReal_mono (μ := euclideanGaussianLaw E) hsub (measure_ne_top _ _)
  rw [measureReal_union hd hR, hneg] at hmass
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := euclideanGaussianLaw E)
    (f := fun z : E => ⟪u, z⟫_ℝ ^ 2) (Eventually.of_forall (fun _ => sq_nonneg _))
    (euclideanGaussian_inner_square_integrable u) (t ^ 2)
  rw [euclideanGaussian_inner_second_moment] at hMarkov
  apply (le_div_iff₀ (by positivity : 0 < 2 * t ^ 2)).mpr
  have h := mul_le_mul_of_nonneg_left hmass (sq_nonneg t)
  nlinarith

theorem gaussianSupportRowLaw_inner_lower_tail (u : E) {r : ℝ} (hr : 0 < r) :
    (gaussianSupportRowLaw E).real {a : Feasible E 2 | ⟪u, a.val⟫_ℝ < -r} ≤
      2 * ‖u‖ ^ 2 / (3 * r ^ 2 * (Module.finrank ℝ E : ℝ)) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hsqrt : 0 < Real.sqrt (Module.finrank ℝ E) := Real.sqrt_pos.mpr hd
  have hs : MeasurableSet {a : E | ⟪u, a⟫_ℝ < -r} :=
    measurableSet_lt (continuous_const.inner continuous_id).measurable measurable_const
  have hmap := congrArg (fun μ : Measure E => μ.real {a : E | ⟪u, a⟫_ℝ < -r})
    (gaussianSupportRowLaw_map (E := E))
  try dsimp only at hmap
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  rw [map_measureReal_apply measurable_subtype_coe hs,
    map_measureReal_apply hm hs] at hmap
  simp only [Set.preimage_setOf_eq] at hmap
  rw [hmap]
  have he : {z : E | ⟪u, (Real.sqrt (Module.finrank ℝ E))⁻¹ • z⟫_ℝ < -r} =
      {z : E | ⟪u, z⟫_ℝ < -(r * Real.sqrt (Module.finrank ℝ E))} := by
    ext z
    simp only [Set.mem_setOf_eq, inner_smul_right, ← div_eq_inv_mul]
    rw [div_lt_iff₀ hsqrt]
    ring_nf
  rw [he]
  have h := (truncatedGaussianLaw_amplification (E := E)
      {z : E | ⟪u, z⟫_ℝ < -(r * Real.sqrt (Module.finrank ℝ E))}).trans
    (mul_le_mul_of_nonneg_left (euclideanGaussian_inner_lower_tail u (mul_pos hr hsqrt))
      (by norm_num : (0 : ℝ) ≤ 4 / 3))
  convert! h using 1
  rw [mul_pow, Real.sq_sqrt hd.le]
  ring

theorem gaussianSupportRowLaw_fixed_direction_tail {k : ℕ} (hk : 0 < k)
    (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512) {u : E} (hu : ‖u‖ ≤ 1) :
    (gaussianSupportRowLaw E).real {a : Feasible E 2 | ⟪u, a.val⟫_ℝ < -((1 : ℝ) / (8 * Real.sqrt k))} ≤
      1 / 8 := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk'
  have h := gaussianSupportRowLaw_inner_lower_tail u (by positivity : (0 : ℝ) < 1 / (8 * Real.sqrt k))
  apply h.trans
  have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have he : 2 * ‖u‖ ^ 2 / (3 * (1 / (8 * Real.sqrt k)) ^ 2 * (Module.finrank ℝ E : ℝ)) =
      128 * (k : ℝ) * ‖u‖ ^ 2 / (3 * (Module.finrank ℝ E : ℝ)) := by
    field_simp
    nlinarith [Real.sq_sqrt hk'.le]
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 3 * (Module.finrank ℝ E : ℝ))).mpr
  have hmul := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 128 * (k : ℝ))
  nlinarith

end
end Nonsmooth
