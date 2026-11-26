import Nonsmooth.RegularVectorNoSpike
import Nonsmooth.SupportProjectionRankCriterion

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Independent regular row laws have a logarithmic actual aggregate posterior
mean increment after observing the maximum and its winning index. -/
theorem regular_vector_support_energy {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (hLp : ∀ i, MemLp (fun z : E => z) 2 (μ i)) {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ i (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → RegularProjectionImage (μ i) u v)
    {c : ℝ} (hc : 0 < c)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2)) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        72 * (1 + 2 * Real.log (4 * ((n + 1 : ℕ) : ℝ))) + 2 * c := by
  obtain ⟨w, hw, huw⟩ := exists_unit_orthogonal_direction hu hd
  apply support_aggregate_shift_of_projection_rank μ u
    (fun i y => regular_projection_image_atomless (μ i) u w (H i w hw huw) y)
    hLp hc (by norm_num : (0 : ℝ) < 72) he hb
  exact fun i => regular_vector_projection_no_spike (μ i) ((hLp i).integrable (by norm_num)) hu hd (H i)

theorem regular_vector_support_log_energy {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (hLp : ∀ i, MemLp (fun z : E => z) 2 (μ i)) {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ i (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → RegularProjectionImage (μ i) u v)
    {c : ℝ} (hc : 0 < c)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2)) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        (504 + 2 * c) * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) := by
  have hs := regular_vector_support_energy μ hLp hu hd H hc he hb
  have hk : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
  have hk0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hlog : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogk : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) := Real.log_nonneg hk
  apply hs.trans
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hk0.ne',
    Real.log_mul (Real.exp_ne_zero _) hk0.ne', Real.log_exp]
  nlinarith [mul_nonneg hc.le hlogk]

end
end Nonsmooth
