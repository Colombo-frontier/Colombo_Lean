import Nonsmooth.PosteriorAggregateEnergy
import Nonsmooth.SupportLoserShift

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem product_row_coordinate_law {k : ℕ} (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin k) :
    (Measure.pi μ).map (fun a : Fin k → E => a i) = μ i :=
  finiteProductKernel_coordinate (fun i => Kernel.const Unit (μ i)) () i

theorem product_rows_memLp_two {k : ℕ} (μ : Fin k → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (hLp : ∀ i, MemLp (fun z : E => z) 2 (μ i)) (i : Fin k) :
    MemLp (fun a : Fin k → E => a i) 2 (Measure.pi μ) := by
  have h := hLp i
  rw [← product_row_coordinate_law μ i] at h
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mp h

theorem supportPosteriorShift_eq_centeredRowMean {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) (i : Fin k) (h : Fin k × ℝ) :
    supportPosteriorShift μ u i h = posteriorCenteredRowMean (Measure.pi μ) (supportSingleObservation u) i h := by
  have hm := integral_map_of_stronglyMeasurable (μ := Measure.pi μ)
    (measurable_pi_apply i) (stronglyMeasurable_id : StronglyMeasurable (fun z : E => z))
  rw [product_row_coordinate_law μ i] at hm
  simp only [id_eq] at hm
  unfold supportPosteriorShift posteriorCenteredRowMean
  rw [← hm]

def supportWinnerShiftEnergy {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) (h : Fin k × ℝ) : ℝ :=
  ‖supportPosteriorShift μ u h.1 h‖ ^ 2

theorem support_shift_energy_partition {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) (h : Fin k × ℝ) :
    (∑ i, ‖supportPosteriorShift μ u i h‖ ^ 2) = supportWinnerShiftEnergy μ u h + supportLoserShiftEnergy μ u h := by
  classical
  have he (i : Fin k) : ‖supportPosteriorShift μ u i h‖ ^ 2 =
      (if i = h.1 then ‖supportPosteriorShift μ u h.1 h‖ ^ 2 else 0) +
        (if i = h.1 then 0 else ‖supportPosteriorShift μ u i h‖ ^ 2) := by
    by_cases hi : i = h.1 <;> simp [hi]
  calc
    _ = ∑ i, ((if i = h.1 then ‖supportPosteriorShift μ u h.1 h‖ ^ 2 else 0) +
        (if i = h.1 then 0 else ‖supportPosteriorShift μ u i h‖ ^ 2)) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, supportWinnerShiftEnergy, supportLoserShiftEnergy]

/-- A bound B for the actual selected-row mean shift implies a bound B+2c for
the actual aggregate posterior mean shift. Independence and all loser terms are
proved internally; the selected-row bound remains an explicit input. -/
theorem support_aggregate_shift_of_winner_bound {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
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
  have hl := support_loser_posterior_shift_bound μ u hzero (fun i => (hLp i).integrable (by norm_num)) hc he hb
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
