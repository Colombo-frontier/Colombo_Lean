import Nonsmooth.MixedLoserShiftEnergy
import Nonsmooth.SupportAggregateCriterion

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem support_aggregate_shift_of_winner_bound_mixed {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hD : ∀ i, (∃ c : ℝ, ∀ᵐ z ∂μ i, ⟪z, u⟫_ℝ = c) ∨
      ∀ y : ℝ, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hLp : ∀ i, MemLp (fun z : E => z) 2 (μ i)) {c B : ℝ} (hc : 0 < c)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2))
    (hwin : (∫ h, supportWinnerShiftEnergy μ u h ∂(Measure.pi μ).map (supportSingleObservation u)) ≤ B) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤ B + 2 * c := by
  let X := supportSingleObservation (k := n + 1) u
  let ρ := (Measure.pi μ).map X
  have hX : Measurable X := supportSingleObservation_measurable u
  letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hp := product_rows_memLp_two μ hLp
  have hprior : iIndepFun (fun i (a : Fin (n + 1) → E) => a i) (Measure.pi μ) :=
    finiteProductKernel_independent (fun i => Kernel.const Unit (μ i)) ()
  have hsum (i : Fin (n + 1)) : Integrable (fun h => ‖supportPosteriorShift μ u i h‖ ^ 2) ρ := by
    have h := posteriorCenteredRowMean_memLp (Measure.pi μ) X hX hp i
    have hnorm := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
    simpa only [supportPosteriorShift_eq_centeredRowMean] using hnorm
  have htotal : Integrable (fun h => ∑ i, ‖supportPosteriorShift μ u i h‖ ^ 2) ρ :=
    integrable_finset_sum _ (fun i _ => hsum i)
  have hl := support_loser_posterior_shift_bound_mixed μ u hD (fun i => (hLp i).integrable (by norm_num)) hc he hb
  have hw : Integrable (supportWinnerShiftEnergy μ u) ρ := by
    apply (htotal.sub hl.1).congr
    apply Eventually.of_forall
    intro h
    dsimp only [Pi.sub_apply]
    linarith [support_shift_energy_partition μ u h]
  have hagg := posterior_aggregate_energy_eq_row_sum (Measure.pi μ) X hX hp hprior
    (supportSingleObservation_posterior_independent μ u)
  calc
    _ = ∑ i, ∫ h, ‖supportPosteriorShift μ u i h‖ ^ 2 ∂ρ := by
      simpa only [supportPosteriorShift_eq_centeredRowMean] using hagg
    _ = ∫ h, ∑ i, ‖supportPosteriorShift μ u i h‖ ^ 2 ∂ρ :=
      (integral_finset_sum _ (fun i _ => hsum i)).symm
    _ = (∫ h, supportWinnerShiftEnergy μ u h ∂ρ) + ∫ h, supportLoserShiftEnergy μ u h ∂ρ := by
      simp_rw [support_shift_energy_partition]
      exact integral_add hw hl.1
    _ ≤ B + 2 * c := add_le_add hwin hl.2

end
end Nonsmooth
