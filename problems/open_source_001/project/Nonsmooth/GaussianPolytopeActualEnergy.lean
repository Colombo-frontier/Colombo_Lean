import Nonsmooth.MixedProjectionEnergy
import Nonsmooth.GaussianPolytopeRowProjectionRank
import Nonsmooth.GaussianPolytopeSelectionClosure
import Nonsmooth.GaussianPolytopeRowConcentration

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeRows_actual_energy {n : ℕ} {s : ℝ} (hs : 0 < s)
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, GaussianPolytopeRow s (μ i)) (u : E) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        (s ^ 2 * 72) * (1 + 2 * Real.log (4 * ((n + 1 : ℕ) : ℝ))) + 2 * s ^ 2 := by
  apply support_aggregate_shift_of_projection_rank_mixed μ u
    (fun i => gaussianPolytopeRow_projection_dichotomy hs (μ i) (hμ i) u)
    (fun i => gaussianPolytopeRow_memLp s (μ i) (hμ i))
    (sq_pos_of_pos hs) (by positivity : 0 < s ^ 2 * 72)
    (fun i v => (gaussianPolytopeRow_vector_centered_mgf s (μ i) (hμ i) v).1)
    (fun i v => (gaussianPolytopeRow_vector_centered_mgf s (μ i) (hμ i) v).2)
  exact fun i => gaussianPolytopeRow_projection_rank hs (μ i) (hμ i) u

theorem gaussianPolytopeRows_actual_log_energy {n : ℕ} {s : ℝ} (hs : 0 < s)
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, GaussianPolytopeRow s (μ i)) (u : E) :
    (∫ h, ‖posteriorAggregateShift (Measure.pi μ) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi μ).map (supportSingleObservation u)) ≤
        512 * s ^ 2 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) := by
  have h := gaussianPolytopeRows_actual_energy hs μ hμ u
  have hk : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
  have hk0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hlog : Real.log (4 : ℝ) ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogk := Real.log_nonneg hk
  have hb : 72 * (1 + 2 * Real.log (4 * ((n + 1 : ℕ) : ℝ))) + 2 ≤
      512 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hk0.ne',
      Real.log_mul (Real.exp_ne_zero _) hk0.ne', Real.log_exp]
    nlinarith
  apply h.trans
  convert mul_le_mul_of_nonneg_left hb (sq_nonneg s) using 1 <;> ring

end
end Nonsmooth
