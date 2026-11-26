import RandomizedFO2003.SphereProjection

namespace RandomizedFO2003.Spherical

open MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A generic invariant probability law on the closed unit ball. This permits
normalized projections that are defined as zero on a zero component. -/
def RotationInvariant (μ : Measure E) : Prop :=
  ∀ U : E ≃ₗᵢ[ℝ] E, MeasurePreserving U μ μ

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem integrable_inner_sq_of_ball (μ : Measure E) [IsProbabilityMeasure μ]
    (hball : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) (v : E) :
    Integrable (fun x => inner (𝕜 := ℝ) v x ^ 2) μ := by
  apply (integrable_const (‖v‖ ^ 2)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
  filter_upwards [hball] with x hx
  have hb : |inner (𝕜 := ℝ) v x| ≤ ‖v‖ :=
    (abs_real_inner_le_norm v x).trans (by nlinarith [norm_nonneg v])
  simpa [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2

theorem invariant_unit_second_moment_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hball : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) (hrot : RotationInvariant μ)
    (v : E) (hv : ‖v‖ = 1) :
    (∫ x, inner (𝕜 := ℝ) v x ^ 2 ∂μ) ≤ 1 / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hsame (i : Fin (Module.finrank ℝ E)) :
      (∫ x, inner (𝕜 := ℝ) (b i) x ^ 2 ∂μ) = ∫ x, inner (𝕜 := ℝ) v x ^ 2 ∂μ := by
    let U : E ≃ₗᵢ[ℝ] E := (Submodule.span ℝ {b i - v})ᗮ.reflection
    have hUv : U (b i) = v := Submodule.reflection_sub (by simp [hv, b])
    have ht := (hrot U).integral_comp U.toHomeomorph.measurableEmbedding
      (fun x => inner (𝕜 := ℝ) v x ^ 2)
    have heq : (fun x => inner (𝕜 := ℝ) v (U x) ^ 2) =
        (fun x => inner (𝕜 := ℝ) (b i) x ^ 2) := by
      funext x
      rw [← hUv, U.inner_map_map]
    rw [heq] at ht
    exact ht
  have hnormint : Integrable (fun x : E => ‖x‖ ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    filter_upwards [hball] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg x]
  have hsum : (∑ i, ∫ x, inner (𝕜 := ℝ) (b i) x ^ 2 ∂μ) ≤ 1 := by
    rw [← integral_finset_sum _ (fun i _ => integrable_inner_sq_of_ball μ hball (b i))]
    calc
      _ = ∫ x, ‖x‖ ^ 2 ∂μ := integral_congr_ae (Filter.Eventually.of_forall (basis_square_sum b))
      _ ≤ ∫ _x, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hnormint (integrable_const _)
        filter_upwards [hball] with x hx
        nlinarith [norm_nonneg x]
      _ = 1 := by simp
  simp_rw [hsame] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  apply (le_div_iff₀ (show (0 : ℝ) < Module.finrank ℝ E by exact_mod_cast Module.finrank_pos)).mpr
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem projection_energy_expansion (W : Submodule ℝ E) (x : E) :
    ‖W.orthogonalProjection x‖ ^ 2 =
      ∑ i, inner (𝕜 := ℝ) ((stdOrthonormalBasis ℝ W) i : E) x ^ 2 := by
  rw [← basis_square_sum (stdOrthonormalBasis ℝ W)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]

omit [Nontrivial E] in
theorem projection_energy_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (hball : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) (W : Submodule ℝ E) :
    Integrable (fun x => ‖W.orthogonalProjection x‖ ^ 2) μ := by
  have hi := integrable_finset_sum Finset.univ
    (fun i _ => integrable_inner_sq_of_ball μ hball ((stdOrthonormalBasis ℝ W) i : E))
  convert hi using 1
  funext x
  exact projection_energy_expansion W x

/-- Mean projection energy into an arbitrary subspace, independent of its
orientation, for a rotationally invariant unit-ball law. -/
theorem invariant_projection_mean_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hball : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) (hrot : RotationInvariant μ) (W : Submodule ℝ E) :
    (∫ x, ‖W.orthogonalProjection x‖ ^ 2 ∂μ) ≤
      (Module.finrank ℝ W : ℝ) / Module.finrank ℝ E := by
  simp_rw [projection_energy_expansion]
  rw [integral_finset_sum _ (fun i _ =>
    integrable_inner_sq_of_ball μ hball ((stdOrthonormalBasis ℝ W) i : E))]
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ W), 1 / (Module.finrank ℝ E : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply invariant_unit_second_moment_le μ hball hrot
      exact (stdOrthonormalBasis ℝ W).norm_eq_one i
    _ = _ := by simp [div_eq_mul_inv]

theorem invariant_projection_tail (μ : Measure E) [IsProbabilityMeasure μ]
    (hball : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) (hrot : RotationInvariant μ)
    (W : Submodule ℝ E) (η : ℝ) (hη : 0 < η) :
    μ {x | η ≤ ‖W.orthogonalProjection x‖} ≤
      ENNReal.ofReal ((Module.finrank ℝ W : ℝ) / ((Module.finrank ℝ E : ℝ) * η ^ 2)) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  have hevent : {x : E | η ≤ ‖W.orthogonalProjection x‖} =
      {x : E | η ^ 2 ≤ ‖W.orthogonalProjection x‖ ^ 2} := by
    ext x
    exact (sq_le_sq₀ hη.le (norm_nonneg (W.orthogonalProjection x))).symm
  rw [hevent]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖W.orthogonalProjection x‖))
    (projection_energy_integrable μ hball W) (η ^ 2)
  change μ.real {x | η ^ 2 ≤ ‖W.orthogonalProjection x‖ ^ 2} ≤ _
  calc
    _ ≤ (∫ x, ‖W.orthogonalProjection x‖ ^ 2 ∂μ) / η ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hη)).mpr (by nlinarith only [hm])
    _ ≤ ((Module.finrank ℝ W : ℝ) / Module.finrank ℝ E) / η ^ 2 :=
      div_le_div_of_nonneg_right (invariant_projection_mean_le μ hball hrot W) (sq_nonneg η)
    _ = _ := by ring

end RandomizedFO2003.Spherical
