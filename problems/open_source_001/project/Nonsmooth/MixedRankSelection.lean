import Nonsmooth.AERankControlledSelection

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem rank_controlled_exponential_moment_mixed (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) {K : ℝ} (hK : 0 < K)
    (hD : (∀ y : ℝ, μ {y} = 0) ∨ ∀ᵐ y ∂μ, f y = 0)
    (hb : ∀ᵐ y ∂μ, f y ≤ K * (1 + rankQuantileLog (cdf μ y))) :
    Integrable (fun y => Real.exp (f y / (2 * K))) μ ∧
      (∫ y, Real.exp (f y / (2 * K)) ∂μ) ≤ 4 * Real.exp (1 / 2 : ℝ) := by
  rcases hD with hatom | hz
  · exact rank_controlled_exponential_moment_ae μ hatom f hf hK hb
  · have he : (fun y => Real.exp (f y / (2 * K))) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
      filter_upwards [hz] with y hy
      rw [hy, zero_div, Real.exp_zero]
    refine ⟨(integrable_const (1 : ℝ)).congr he.symm, ?_⟩
    rw [integral_congr_ae he, integral_const, measureReal_univ_eq_one, one_smul]
    have hp : 1 ≤ Real.exp (1 / 2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    linarith

theorem selected_rank_controlled_energy_mixed {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ} [Nonempty (Fin k)]
    (X : Fin k → α → ℝ) (hX : ∀ i, Measurable (X i))
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hD : ∀ i, (∀ y : ℝ, (μ.map (X i)) {y} = 0) ∨ ∀ᵐ y ∂μ.map (X i), f i y = 0)
    {K : ℝ} (hK : 0 < K)
    (hb : ∀ i, ∀ᵐ y ∂μ.map (X i), f i y ≤ K * (1 + rankQuantileLog (cdf (μ.map (X i)) y)))
    (Z : α → ℝ) (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (hsel : ∀ x, ∃ i, Z x ≤ f i (X i x)) :
    Integrable Z μ ∧ (∫ x, Z x ∂μ) ≤ K * (1 + 2 * Real.log (4 * (k : ℝ))) := by
  have he (i : Fin k) :
      Integrable (fun x => Real.exp ((1 / (2 * K)) * f i (X i x))) μ ∧
        (∫ x, Real.exp ((1 / (2 * K)) * f i (X i x)) ∂μ) ≤ 4 * Real.exp (1 / 2 : ℝ) := by
    letI : IsProbabilityMeasure (μ.map (X i)) := Measure.isProbabilityMeasure_map (hX i).aemeasurable
    have h := rank_controlled_exponential_moment_mixed (μ.map (X i)) (f i) (hf i) hK (hD i) (hb i)
    have hm : StronglyMeasurable (fun y => Real.exp (f i y / (2 * K))) :=
      (Real.continuous_exp.measurable.comp ((hf i).div_const _)).stronglyMeasurable
    have hi := (integrable_map_measure hm.aestronglyMeasurable (hX i).aemeasurable).mp h.1
    have hi' : Integrable (fun x => Real.exp ((1 / (2 * K)) * f i (X i x))) μ := by
      convert hi using 1
      funext x
      congr 1
      ring
    refine ⟨hi', ?_⟩
    have hbound := h.2
    rw [integral_map_of_stronglyMeasurable (hX i) hm] at hbound
    convert hbound using 1
    congr 1
    funext x
    congr 1
    ring
  have hs := selected_nonnegative_energy_of_exponential μ (fun i x => f i (X i x)) Z hZ hZ0
    (by positivity : 0 < 1 / (2 * K)) (by positivity : 0 < 4 * Real.exp (1 / 2 : ℝ))
    (fun i => (he i).1) (fun i => (he i).2) hsel
  refine ⟨hs.1, hs.2.trans_eq ?_⟩
  have hk : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by simpa only [Fintype.card_fin] using
      (Fintype.card_pos : 0 < Fintype.card (Fin k)))
  rw [show (k : ℝ) * (4 * Real.exp (1 / 2 : ℝ)) =
      (4 * (k : ℝ)) * Real.exp (1 / 2 : ℝ) by ring,
    Real.log_mul (by positivity : (4 * (k : ℝ)) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring

end
end Nonsmooth
