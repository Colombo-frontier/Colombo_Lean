import Nonsmooth.GaussianSupportPosterior

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem rotational_coordinate_moment_equal (μ : Measure E)
    (hinv : ∀ e : E ≃ₗᵢ[ℝ] E, μ.map e = μ) {u v : E} (hn : ‖u‖ = ‖v‖) :
    (∫ x : E, ⟪u, x⟫_ℝ ^ 2 ∂μ) = ∫ x : E, ⟪v, x⟫_ℝ ^ 2 ∂μ := by
  let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (u - v))ᗮ.reflection
  have heu : e u = v := Submodule.reflection_sub hn
  have hp : MeasurePreserving e μ μ := ⟨e.continuous.measurable, hinv e⟩
  calc
    _ = ∫ x : E, ⟪v, e x⟫_ℝ ^ 2 ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change ⟪u, x⟫_ℝ ^ 2 = ⟪v, e x⟫_ℝ ^ 2
      rw [← heu, e.inner_map_map]
    _ = _ := hp.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun x : E => ⟪v, x⟫_ℝ ^ 2)

theorem rotational_unit_second_moment (μ : Measure E)
    (hinv : ∀ e : E ≃ₗᵢ[ℝ] E, μ.map e = μ) (hV : MemLp (fun x : E => x) 2 μ)
    {u : E} (hu : ‖u‖ = 1) :
    (∫ x : E, ⟪u, x⟫_ℝ ^ 2 ∂μ) = (∫ x : E, ‖x‖ ^ 2 ∂μ) / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hb (i : Fin (Module.finrank ℝ E)) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hi (i : Fin (Module.finrank ℝ E)) : Integrable (fun x => ⟪b i, x⟫_ℝ ^ 2) μ :=
    (hV.const_inner (b i)).integrable_sq
  have he (i : Fin (Module.finrank ℝ E)) :
      (∫ x, ⟪b i, x⟫_ℝ ^ 2 ∂μ) = ∫ x, ⟪u, x⟫_ℝ ^ 2 ∂μ :=
    rotational_coordinate_moment_equal μ hinv ((hb i).trans hu.symm)
  have hs (x : E) : (∑ i, ⟪b i, x⟫_ℝ ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right x
  have hsum : (Module.finrank ℝ E : ℝ) * (∫ x, ⟪u, x⟫_ℝ ^ 2 ∂μ) = ∫ x, ‖x‖ ^ 2 ∂μ := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E), ∫ x, ⟪b i, x⟫_ℝ ^ 2 ∂μ := by
        simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x, ∑ i, ⟪b i, x⟫_ℝ ^ 2 ∂μ := (integral_finset_sum _ (fun i _ => hi i)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall hs)
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  apply (eq_div_iff hd.ne').mpr
  nlinarith

theorem rotational_second_moment (μ : Measure E)
    (hinv : ∀ e : E ≃ₗᵢ[ℝ] E, μ.map e = μ) (hV : MemLp (fun x : E => x) 2 μ) (u : E) :
    (∫ x : E, ⟪u, x⟫_ℝ ^ 2 ∂μ) =
      ‖u‖ ^ 2 * (∫ x : E, ‖x‖ ^ 2 ∂μ) / (Module.finrank ℝ E : ℝ) := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have he : ‖u‖ • normalizedDirection u = u := by simp [normalizedDirection, smul_smul, hn]
  calc
    _ = ∫ x, ‖u‖ ^ 2 * ⟪normalizedDirection u, x⟫_ℝ ^ 2 ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change ⟪u, x⟫_ℝ ^ 2 = ‖u‖ ^ 2 * ⟪normalizedDirection u, x⟫_ℝ ^ 2
      conv_lhs => rw [← he, real_inner_smul_left, mul_pow]
    _ = _ := by
      rw [integral_const_mul, rotational_unit_second_moment μ hinv hV (normalizedDirection_norm hu)]
      ring

end
end Nonsmooth
