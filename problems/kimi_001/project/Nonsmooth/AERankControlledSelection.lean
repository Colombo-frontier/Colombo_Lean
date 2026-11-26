import Nonsmooth.RankControlledSelection

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A rank bound only needs to hold almost everywhere under the actual marginal.
Clipping on the exceptional set reduces it to the everywhere version. -/
theorem rank_controlled_exponential_moment_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) (f : ℝ → ℝ) (hf : Measurable f)
    {K : ℝ} (hK : 0 < K)
    (hb : ∀ᵐ y ∂μ, f y ≤ K * (1 + rankQuantileLog (cdf μ y))) :
    Integrable (fun y => Real.exp (f y / (2 * K))) μ ∧
      (∫ y, Real.exp (f y / (2 * K)) ∂μ) ≤ 4 * Real.exp (1 / 2 : ℝ) := by
  let g : ℝ → ℝ := fun y => min (f y) (K * (1 + rankQuantileLog (cdf μ y)))
  have hgm : Measurable g := by
    have hc := (continuous_cdf_of_atomless μ hμ).measurable
    dsimp only [g, rankQuantileLog]
    fun_prop
  have h := rank_controlled_exponential_moment μ hμ g hgm hK (fun y => min_le_right _ _)
  have he : (fun y => Real.exp (g y / (2 * K))) =ᵐ[μ] (fun y => Real.exp (f y / (2 * K))) := by
    filter_upwards [hb] with y hy
    dsimp only [g]
    rw [min_eq_left hy]
  exact ⟨h.1.congr he, (integral_congr_ae he).symm.trans_le h.2⟩

theorem selected_rank_controlled_energy_ae {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ} [Nonempty (Fin k)]
    (X : Fin k → α → ℝ) (hX : ∀ i, Measurable (X i))
    (hatom : ∀ i y, (μ.map (X i)) {y} = 0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    {K : ℝ} (hK : 0 < K)
    (hb : ∀ i, ∀ᵐ y ∂μ.map (X i), f i y ≤ K * (1 + rankQuantileLog (cdf (μ.map (X i)) y)))
    (Z : α → ℝ) (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (hsel : ∀ x, ∃ i, Z x ≤ f i (X i x)) :
    Integrable Z μ ∧ (∫ x, Z x ∂μ) ≤ K * (1 + 2 * Real.log (4 * (k : ℝ))) := by
  have he (i : Fin k) :
      Integrable (fun x => Real.exp ((1 / (2 * K)) * f i (X i x))) μ ∧
        (∫ x, Real.exp ((1 / (2 * K)) * f i (X i x)) ∂μ) ≤ 4 * Real.exp (1 / 2 : ℝ) := by
    letI : IsProbabilityMeasure (μ.map (X i)) := Measure.isProbabilityMeasure_map (hX i).aemeasurable
    have h := rank_controlled_exponential_moment_ae (μ.map (X i)) (hatom i) (f i) (hf i) hK (hb i)
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
