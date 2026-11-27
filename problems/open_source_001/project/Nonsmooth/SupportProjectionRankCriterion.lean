import Nonsmooth.SupportWinnerRank
import Nonsmooth.AEDirectionalNorm

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The actual aggregate mean energy for independent, possibly different row
laws is logarithmic once the one-row projection rank bounds are established. -/
theorem support_aggregate_shift_of_projection_rank {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hLp : ∀ i, MemLp (fun z : E => z) 2 (μ i)) {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2))
    (hrank : ∀ i, ∀ᵐ y ∂(μ i).map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift (μ i) u y‖ ^ 2 ≤
        K * (1 + rankQuantileLog (cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y))) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        K * (1 + 2 * Real.log (4 * ((n + 1 : ℕ) : ℝ))) + 2 * c :=
  support_aggregate_shift_of_winner_bound μ u hzero hLp hc he hb
    (support_winner_energy_of_projection_rank μ u hzero hK hrank).2

theorem support_aggregate_shift_of_directional_rank {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hLp : ∀ i, MemLp (fun z : E => z) 2 (μ i)) {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2))
    (hrank : ∀ i (v : E), ∀ᵐ y ∂(μ i).map (fun z : E => ⟪z, u⟫_ℝ),
      ⟪v, projectionPosteriorShift (μ i) u y⟫_ℝ ^ 2 ≤
        ‖v‖ ^ 2 * (K * (1 + rankQuantileLog (cdf ((μ i).map (fun z : E => ⟪z, u⟫_ℝ)) y)))) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        K * (1 + 2 * Real.log (4 * ((n + 1 : ℕ) : ℝ))) + 2 * c := by
  apply support_aggregate_shift_of_projection_rank μ u hzero hLp hc hK he hb
  intro i
  exact ae_norm_sq_le_of_directional_inner_bound_nontrivial _ _ _ (hrank i)

end
end Nonsmooth
