import Nonsmooth.RegularVectorConcentration
import Nonsmooth.RegularVectorSupportEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A complete logarithmic one-step estimate for the regular vector class.
Row moments, centered MGFs, atomlessness, winner and loser energies, posterior
independence and cross-term cancellation are all proved from the image data. -/
theorem regular_vector_support_log_energy_of_images {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ i (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → RegularProjectionImage (μ i) u v) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        512 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) := by
  have hLp := fun i => regular_vector_memLp_two (μ i) hu hd (H i)
  have he := fun i v => regular_vector_centered_concentration (μ i) hu hd (H i) v
  have hb (i : Fin (n + 1)) (v : E) :
      (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (4 * ‖v‖ ^ 2 / 2) := by
    convert (he i v).2 using 1
    congr 1
    ring
  have hs := regular_vector_support_log_energy μ hLp hu hd H (by norm_num : (0 : ℝ) < 4)
    (fun i v => (he i v).1) hb
  simpa only [show (504 : ℝ) + 2 * 4 = 512 by norm_num] using hs

end
end Nonsmooth
