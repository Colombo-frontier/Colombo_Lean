import Nonsmooth.GeneralMaximumShift
import Nonsmooth.MixedSelectionLoserKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem support_loser_posterior_shift_bound_mixed {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hD : ∀ i, (∃ c : ℝ, ∀ᵐ z ∂μ i, ⟪z, u⟫_ℝ = c) ∨
      ∀ y : ℝ, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hi : ∀ i, Integrable (fun z : E => z) (μ i)) {c : ℝ} (hc : 0 < c)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2)) :
    Integrable (supportLoserShiftEnergy μ u) ((Measure.pi μ).map (supportSingleObservation u)) ∧
      (∫ h, supportLoserShiftEnergy μ u h ∂(Measure.pi μ).map (supportSingleObservation u)) ≤ 2 * c := by
  let ρ := (Measure.pi μ).map (supportSingleObservation u)
  let F : ℝ → ℝ := fun y => ∑ i, ‖halfspacePosteriorShift (μ i) u y‖ ^ 2
  have hFm : Measurable F := by
    have hm (i : Fin (n + 1)) := halfspacePosteriorShift_measurable (μ i) u
    dsimp only [F]
    fun_prop
  have hmap : ρ.map Prod.snd = supportResponseLaw μ u := by
    rw [Measure.map_map measurable_snd (supportSingleObservation_measurable u)]
    rfl
  have hcost := maximum_total_halfspace_shift_general μ u hi hc he hb
  change Integrable F (supportResponseLaw μ u) ∧ (∫ y, F y ∂supportResponseLaw μ u) ≤ 2 * c at hcost
  rw [← hmap] at hcost
  have hright : Integrable (fun h : Fin (n + 1) × ℝ => F h.2) ρ :=
    (integrable_map_measure hFm.aestronglyMeasurable measurable_snd.aemeasurable).mp hcost.1
  have hbound : supportLoserShiftEnergy μ u ≤ᵐ[ρ] (fun h => F h.2) := by
    filter_upwards [supportPosteriorShift_loser_ae_mixed μ u hD] with h hh
    apply Finset.sum_le_sum
    intro i _
    by_cases hni : i = h.1
    · simp only [hni, if_pos rfl]
      exact sq_nonneg _
    · simp only [if_neg hni, hh i hni]
      exact le_rfl
  have hnonneg (h : Fin (n + 1) × ℝ) : 0 ≤ supportLoserShiftEnergy μ u h := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hleft : Integrable (supportLoserShiftEnergy μ u) ρ := by
    apply hright.mono' (supportLoserShiftEnergy_measurable μ u).aestronglyMeasurable
    filter_upwards [hbound] with h hh
    simpa only [Real.norm_of_nonneg (hnonneg h)] using hh
  refine ⟨hleft, (integral_mono_ae hleft hright hbound).trans ?_⟩
  simpa only [integral_map_of_stronglyMeasurable measurable_snd hFm.stronglyMeasurable] using hcost.2

end
end Nonsmooth
