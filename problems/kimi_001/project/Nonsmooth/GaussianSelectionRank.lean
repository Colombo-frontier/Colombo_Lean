import Nonsmooth.ContinuousRank

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem supportLoserRegion_ae_halfspace (μ : Measure E) {u : E}
    (hzero : ∀ y : ℝ, μ {z : E | ⟪z, u⟫_ℝ = y} = 0)
    {k : ℕ} (w i : Fin k) (y : ℝ) :
    (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) =ᵐ[μ] {z : E | ⟪z, u⟫_ℝ ≤ y} := by
  have hne : ∀ᵐ z ∂μ, ⟪z, u⟫_ℝ ≠ y := by
    rw [ae_iff]
    simpa only [not_not] using hzero y
  filter_upwards [hne] with z hz
  apply propext
  change (⟪z, u⟫_ℝ ≤ y ∧ (¬i < w ∨ ⟪z, u⟫_ℝ < y)) ↔ ⟪z, u⟫_ℝ ≤ y
  exact ⟨And.left, fun h => ⟨h, Or.inr (lt_of_le_of_ne h hz)⟩⟩

variable [Nontrivial E]

instance gaussianProjectionLaw_probability (u : E) :
    IsProbabilityMeasure ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) := by
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  exact Measure.isProbabilityMeasure_map hr.aemeasurable

theorem gaussianProjectionLaw_atomless {u : E} (hu : u ≠ 0) :
    ∀ y : ℝ, ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) {y} = 0 := by
  intro y
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  rw [Measure.map_apply hr (measurableSet_singleton y)]
  simpa only [Set.preimage, mem_singleton_iff, real_inner_comm u] using
    gaussianAmbientRow_hyperplane_zero hu y

theorem gaussianSelection_loser_mass {u : E} (hu : u ≠ 0) {k : ℕ} (w i : Fin k) (y : ℝ) :
    gaussianAmbientRowLaw E (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) =
      ENNReal.ofReal (cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y) := by
  have hzero (t : ℝ) : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ = t} = 0 := by
    simpa only [real_inner_comm u] using gaussianAmbientRow_hyperplane_zero hu t
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  rw [measure_congr (supportLoserRegion_ae_halfspace (gaussianAmbientRowLaw E) hzero w i y),
    ofReal_cdf, Measure.map_apply hr measurableSet_Iic]
  rfl

theorem gaussianSelection_value_density {u : E} (hu : u ≠ 0) {n : ℕ} (w : Fin (n + 1)) :
    supportSelectionValueLaw (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w =
      ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)).withDensity (fun y =>
        (ENNReal.ofReal (cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y)) ^ n) := by
  unfold supportSelectionValueLaw supportSelectionWeight
  simp_rw [gaussianSelection_loser_mass hu]
  simp

/-- For a specified winning index, the CDF-rank law has density p^n on (0,1], for n other rows.
This is a subprobability measure; summing over the n+1 winners gives the maximum-rank law. -/
theorem gaussianSelection_value_rank_law {u : E} (hu : u ≠ 0) {n : ℕ} (w : Fin (n + 1)) :
    (supportSelectionValueLaw (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w).map
      (cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ))) =
      ((volume : Measure ℝ).restrict (Ioc 0 1)).withDensity (fun p => (ENNReal.ofReal p) ^ n) := by
  rw [gaussianSelection_value_density hu]
  exact atomless_cdf_weighted_map _ (gaussianProjectionLaw_atomless hu)
    (fun p : ℝ => (ENNReal.ofReal p) ^ n) (measurable_id.ennreal_ofReal.pow_const n)

theorem gaussianSelection_rank_integral {u : E} (hu : u ≠ 0) {n : ℕ} (w : Fin (n + 1))
    (f : ℝ → ℝ) (hf : StronglyMeasurable f) :
    (∫ y, f (cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y)
      ∂supportSelectionValueLaw (fun _ : Fin (n + 1) => gaussianAmbientRowLaw E) u w) =
      ∫ p in Ioc (0 : ℝ) 1, p ^ n * f p := by
  have hcdf := (continuous_cdf_of_atomless _ (gaussianProjectionLaw_atomless hu)).measurable
  have hw : Measurable (fun p : ℝ => (ENNReal.ofReal p) ^ n) := measurable_id.ennreal_ofReal.pow_const n
  rw [← integral_map_of_stronglyMeasurable hcdf hf, gaussianSelection_value_rank_law hu,
    integral_withDensity_eq_integral_toReal_smul
      hw
      (Eventually.of_forall (fun p : ℝ => ENNReal.pow_lt_top (ENNReal.ofReal_lt_top))) ]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with p hp
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hp.1.le, smul_eq_mul]

end
end Nonsmooth
