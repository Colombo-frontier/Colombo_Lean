import FreshGradientMinimax.RelativeEstimator

/-! The noise-free endpoint is a deterministic finite computation.
This is proved from the original oracle's zero variance, not assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

theorem probability_eq_dirac_of_square_error_le_zero {d : ℕ} (ν : Measure (Euclid d))
    [IsProbabilityMeasure ν] (g : Euclid d)
    (hi : Integrable (fun r => ‖r - g‖ ^ 2) ν) (hz : (∫ r, ‖r - g‖ ^ 2 ∂ν) ≤ 0) :
    ν = Measure.dirac g := by
  have hzero : (∫ r, ‖r - g‖ ^ 2 ∂ν) = 0 := le_antisymm hz (integral_nonneg (fun _ => sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hzero
  have he : (fun r : Euclid d => r) =ᵐ[ν] (fun _ => g) := by
    filter_upwards [hae] with r hr
    have hn : ‖r - g‖ = 0 := sq_eq_zero_iff.mp hr
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hmap : Measure.map (fun r : Euclid d => r) ν = Measure.map (fun _ => g) ν :=
    Measure.map_congr he
  change Measure.map id ν = Measure.map (fun _ => g) ν at hmap
  simpa only [Measure.map_id, Measure.map_const, measure_univ, one_smul] using hmap

namespace FreshOracle
variable {dx dy : ℕ} {L μ : ℝ} {O : NCObjective dx dy L μ}

theorem primal_batch_zero_noise (K : FreshOracle O 0) (z : Joint dx dy) {b : ℕ} (hb : 0 < b) :
    batchKernel K.primalKernel b z = Measure.dirac (O.gradX z.1 z.2) := by
  obtain ⟨_, _, hi, hv⟩ := K.primal_batch_contract z hb
  apply probability_eq_dirac_of_square_error_le_zero _ _ hi
  simpa using hv

theorem dual_batch_zero_noise (K : FreshOracle O 0) (z : Joint dx dy) {b : ℕ} (hb : 0 < b) :
    batchKernel K.dualKernel b z = Measure.dirac (O.gradY z.1 z.2) := by
  obtain ⟨_, _, hi, hv⟩ := K.dual_batch_contract z hb
  apply probability_eq_dirac_of_square_error_le_zero _ _ hi
  simpa using hv

end FreshOracle
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

def fastExactPoint (v : Euclid dy) : ℕ → Euclid dx → Euclid dx
  | 0, u => u
  | n + 1, u => fastExactPoint v n u - ℓ⁻¹ • S.gradX (fastExactPoint v n u) v

theorem fastStepKernel_zero_noise (O : FreshOracle S.toNCObjective 0) {b : ℕ} (hb : 0 < b)
    (v : Euclid dy) (u : Euclid dx) :
    S.fastStepKernel O b v u = Measure.dirac (u - ℓ⁻¹ • S.gradX u v) := by
  rw [S.fastStepKernel_apply, O.primal_batch_zero_noise _ hb,
    Measure.map_dirac (f := fun r : Euclid dx => u - ℓ⁻¹ • r)
      (measurable_const.sub (measurable_const.smul measurable_id))]

theorem fastRunKernel_zero_noise (O : FreshOracle S.toNCObjective 0) {b : ℕ} (hb : 0 < b)
    (v : Euclid dy) (n : ℕ) (u : Euclid dx) :
    S.fastRunKernel O b v n u = Measure.dirac (S.fastExactPoint v n u) := by
  induction n with
  | zero => simp only [fastRunKernel, iterateKernel, Kernel.id_apply, fastExactPoint]
  | succ n ih =>
    change (S.fastStepKernel O b v ∘ₖ S.fastRunKernel O b v n) u = _
    rw [Kernel.comp_apply, ih, Measure.dirac_bind (Kernel.measurable _), S.fastStepKernel_zero_noise O hb]
    rfl

theorem levelReadKernel_zero_noise (O : FreshOracle S.toNCObjective 0) {b : ℕ} (hb : 0 < b)
    (v a : Euclid dy) (u : Euclid dx) :
    S.levelReadKernel O b v a u = Measure.dirac (-S.gradY u v + a) := by
  rw [S.levelReadKernel_apply, O.dual_batch_zero_noise _ hb,
    Measure.map_dirac (f := fun r : Euclid dy => -r + a) (measurable_id.neg.add measurable_const)]

theorem levelKernel_zero_noise (O : FreshOracle S.toNCObjective 0) {b : ℕ} (hb : 0 < b)
    (n : ℕ) (v a : Euclid dy) (u : Euclid dx) :
    S.levelKernel O b n v a u = Measure.dirac (-S.gradY (S.fastExactPoint v n u) v + a) := by
  rw [levelKernel, Kernel.comp_apply, S.fastRunKernel_zero_noise O hb,
    Measure.dirac_bind (Kernel.measurable _), S.levelReadKernel_zero_noise O hb]

theorem relativeEstimatorKernel_zero_noise (O : FreshOracle S.toNCObjective 0) (ρ m e : ℝ)
    (v a : Euclid dy) (u : Euclid dx) :
    S.relativeEstimatorKernel O ρ m e v a u =
      Measure.dirac (-S.gradY (S.fastExactPoint v (levelSteps ℓ α (ρ / 14) m 1) u) v + a) := by
  simpa [relativeEstimatorKernel, estimatorCutoff, multilevelKernel, estimatorGamma] using
    S.levelKernel_zero_noise O (by decide : 0 < (1 : ℕ)) (levelSteps ℓ α (ρ / 14) m 1) v a u

theorem relativeEstimatorKernel_zero_variance (O : FreshOracle S.toNCObjective 0) (ρ m e : ℝ)
    (v a : Euclid dy) (u : Euclid dx) :
    (∫ r, ‖r - ∫ z, z ∂S.relativeEstimatorKernel O ρ m e v a u‖ ^ 2
      ∂S.relativeEstimatorKernel O ρ m e v a u) = 0 := by
  rw [S.relativeEstimatorKernel_zero_noise]
  simp

end SCObjective
end FreshGradientMinimax
