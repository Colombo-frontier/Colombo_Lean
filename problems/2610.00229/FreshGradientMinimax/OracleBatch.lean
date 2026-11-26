import FreshGradientMinimax.BatchKernel
import FreshGradientMinimax.GradientDescent

/-! Projecting the original joint oracle and averaging fresh draws. Every
sample is a one-point call to the fixed joint kernel; discarded coordinates
do not introduce a new oracle interface. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace FreshOracle
variable {dx dy : ℕ} {L μ σ : ℝ} {O : NCObjective dx dy L μ} (K : FreshOracle O σ)

def primalKernel : Kernel (Joint dx dy) (Euclid dx) := K.kernel.map Prod.fst
def dualKernel : Kernel (Joint dx dy) (Euclid dy) := K.kernel.map Prod.snd

instance primalKernel_markov : IsMarkovKernel K.primalKernel :=
  Kernel.IsMarkovKernel.map _ measurable_fst
instance dualKernel_markov : IsMarkovKernel K.dualKernel :=
  Kernel.IsMarkovKernel.map _ measurable_snd

theorem primalKernel_contract (z : Joint dx dy) :
    Integrable id (K.primalKernel z) ∧ (∫ r, r ∂K.primalKernel z) = O.gradX z.1 z.2 ∧
      Integrable (fun r => ‖r - O.gradX z.1 z.2‖ ^ 2) (K.primalKernel z) ∧
      (∫ r, ‖r - O.gradX z.1 z.2‖ ^ 2 ∂K.primalKernel z) ≤ σ ^ 2 := by
  have hb (r : Joint dx dy) : ‖r.1 - O.gradX z.1 z.2‖ ^ 2 ≤ jointNormSq (r - O.jointGradient z) := by
    dsimp [jointNormSq, NCObjective.jointGradient]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hv : Integrable (fun r : Joint dx dy => ‖r.1 - O.gradX z.1 z.2‖ ^ 2) (K.kernel z) := by
    apply (K.square_integrable z).mono' ((continuous_fst.sub continuous_const).norm.pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb r)
  have hmean : (∫ r : Joint dx dy, r.1 ∂K.kernel z) = O.gradX z.1 z.2 := by
    calc
      _ = (∫ r, r ∂K.kernel z).1 := by simpa only [id_eq] using (fst_integral (K.integrable z)).symm
      _ = _ := by rw [K.mean]; rfl
  have hmap : K.primalKernel z = (K.kernel z).map Prod.fst := Kernel.map_apply _ measurable_fst z
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmap]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr
      (K.integrable z).fst
  · rw [hmap, integral_map (f := fun r : Euclid dx => r) measurable_fst.aemeasurable
      measurable_id.aestronglyMeasurable]
    exact hmean
  · rw [hmap]
    exact (integrable_map_measure (g := fun r : Euclid dx => ‖r - O.gradX z.1 z.2‖ ^ 2)
      ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hv
  · rw [hmap, integral_map (f := fun r : Euclid dx => ‖r - O.gradX z.1 z.2‖ ^ 2)
      measurable_fst.aemeasurable ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable]
    exact (integral_mono hv (K.square_integrable z) hb).trans (K.variance_le z)

theorem dualKernel_contract (z : Joint dx dy) :
    Integrable id (K.dualKernel z) ∧ (∫ r, r ∂K.dualKernel z) = O.gradY z.1 z.2 ∧
      Integrable (fun r => ‖r - O.gradY z.1 z.2‖ ^ 2) (K.dualKernel z) ∧
      (∫ r, ‖r - O.gradY z.1 z.2‖ ^ 2 ∂K.dualKernel z) ≤ σ ^ 2 := by
  have hb (r : Joint dx dy) : ‖r.2 - O.gradY z.1 z.2‖ ^ 2 ≤ jointNormSq (r - O.jointGradient z) := by
    dsimp [jointNormSq, NCObjective.jointGradient]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hv : Integrable (fun r : Joint dx dy => ‖r.2 - O.gradY z.1 z.2‖ ^ 2) (K.kernel z) := by
    apply (K.square_integrable z).mono' ((continuous_snd.sub continuous_const).norm.pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb r)
  have hmean : (∫ r : Joint dx dy, r.2 ∂K.kernel z) = O.gradY z.1 z.2 := by
    calc
      _ = (∫ r, r ∂K.kernel z).2 := by simpa only [id_eq] using (snd_integral (K.integrable z)).symm
      _ = _ := by rw [K.mean]; rfl
  have hmap : K.dualKernel z = (K.kernel z).map Prod.snd := Kernel.map_apply _ measurable_snd z
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmap]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable measurable_snd.aemeasurable).mpr
      (K.integrable z).snd
  · rw [hmap, integral_map (f := fun r : Euclid dy => r) measurable_snd.aemeasurable
      measurable_id.aestronglyMeasurable]
    exact hmean
  · rw [hmap]
    exact (integrable_map_measure (g := fun r : Euclid dy => ‖r - O.gradY z.1 z.2‖ ^ 2)
      ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
      measurable_snd.aemeasurable).mpr hv
  · rw [hmap, integral_map (f := fun r : Euclid dy => ‖r - O.gradY z.1 z.2‖ ^ 2)
      measurable_snd.aemeasurable ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable]
    exact (integral_mono hv (K.square_integrable z) hb).trans (K.variance_le z)

theorem primal_batch_contract (z : Joint dx dy) {b : ℕ} (hb : 0 < b) :
    Integrable id (batchKernel K.primalKernel b z) ∧
      (∫ r, r ∂batchKernel K.primalKernel b z) = O.gradX z.1 z.2 ∧
      Integrable (fun r => ‖r - O.gradX z.1 z.2‖ ^ 2) (batchKernel K.primalKernel b z) ∧
      (∫ r, ‖r - O.gradX z.1 z.2‖ ^ 2 ∂batchKernel K.primalKernel b z) ≤ σ ^ 2 / b := by
  obtain ⟨hi, hm, hv, hbnd⟩ := K.primalKernel_contract z
  obtain ⟨hi', hm', hv', _⟩ := batchKernel_moments K.primalKernel z _ hi hm hv hb
  exact ⟨hi', hm', hv', batchKernel_variance_le K.primalKernel z _ hi hm hv hbnd hb⟩

theorem dual_batch_contract (z : Joint dx dy) {b : ℕ} (hb : 0 < b) :
    Integrable id (batchKernel K.dualKernel b z) ∧
      (∫ r, r ∂batchKernel K.dualKernel b z) = O.gradY z.1 z.2 ∧
      Integrable (fun r => ‖r - O.gradY z.1 z.2‖ ^ 2) (batchKernel K.dualKernel b z) ∧
      (∫ r, ‖r - O.gradY z.1 z.2‖ ^ 2 ∂batchKernel K.dualKernel b z) ≤ σ ^ 2 / b := by
  obtain ⟨hi, hm, hv, hbnd⟩ := K.dualKernel_contract z
  obtain ⟨hi', hm', hv', _⟩ := batchKernel_moments K.dualKernel z _ hi hm hv hb
  exact ⟨hi', hm', hv', batchKernel_variance_le K.dualKernel z _ hi hm hv hbnd hb⟩

end FreshOracle
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem fast_batch_contraction (K : FreshOracle S.toNCObjective σ)
    (u : Euclid dx) (v : Euclid dy) {b : ℕ} (hb : 0 < b) :
    (∫ r, ‖u - ℓ⁻¹ • r - S.sliceMin v‖ ^ 2 ∂batchKernel K.primalKernel b (u, v)) ≤
      (1 - α / ℓ) * ‖u - S.sliceMin v‖ ^ 2 + σ ^ 2 / (ℓ ^ 2 * b) := by
  obtain ⟨hi, hm, hv, hvar⟩ := K.primal_batch_contract (u, v) hb
  have h := noisy_gradient_step_contraction S.toNCObjective.L_pos
    (fun x => S.toNCObjective.derivative_x x v) (fun x y => S.toNCObjective.gradX_lip_primal x y v)
    (S.primal_strong v) (S.sliceMin v) (S.sliceMin_minimizes v) u id hi hm hv hvar
  convert h using 1
  ring

end SCObjective
end FreshGradientMinimax
