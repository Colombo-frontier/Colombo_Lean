import FreshGradientMinimax.FastIteration
import FreshGradientMinimax.EffectiveObjective

/-! One finite level H_j of F.1: run adaptive fast-variable minibatch descent,
then draw a fresh dual minibatch. The second moment is proved for the actual
composed kernel around the true effective gradient, including a known additive
regularization gradient. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def levelReadKernel (K : FreshOracle S.toNCObjective σ) (b : ℕ) (v a : Euclid dy) :
    Kernel (Euclid dx) (Euclid dy) :=
  ((batchKernel K.dualKernel b).comap (fun u => (u, v)) (measurable_id.prodMk measurable_const)).map
    (fun r => -r + a)

instance levelReadKernel_markov (K : FreshOracle S.toNCObjective σ) (b : ℕ) (v a : Euclid dy) :
    IsMarkovKernel (S.levelReadKernel K b v a) :=
  Kernel.IsMarkovKernel.map _ (measurable_id.neg.add measurable_const)

theorem levelReadKernel_apply (K : FreshOracle S.toNCObjective σ) (b : ℕ)
    (v a : Euclid dy) (u : Euclid dx) :
    S.levelReadKernel K b v a u = (batchKernel K.dualKernel b (u, v)).map (fun r => -r + a) := by
  rw [levelReadKernel, Kernel.map_apply (f := fun r : Euclid dy => -r + a) _
    (measurable_id.neg.add measurable_const), Kernel.comap_apply]

theorem levelReadKernel_square_integrable (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (v a : Euclid dy) (u : Euclid dx) :
    Integrable (fun r => ‖r - (gradient S.effectiveValue v + a)‖ ^ 2) (S.levelReadKernel K b v a u) := by
  obtain ⟨hi, hm, hv, hvar⟩ := K.dual_batch_contract (u, v) hb
  have hs := square_integrable_of_centered hi (S.gradY u v) hv
  have ht := integrable_square_sub_const hi hs (S.gradY (S.sliceMin v) v)
  have he (r : Euclid dy) : ‖(-r + a) - (gradient S.effectiveValue v + a)‖ ^ 2 =
      ‖r - S.gradY (S.sliceMin v) v‖ ^ 2 := by
    rw [S.true_effective_gradient, effectiveGradient]
    congr 1
    rw [show (-r + a) - (-S.gradY (S.sliceMin v) v + a) = -(r - S.gradY (S.sliceMin v) v) by abel,
      norm_neg]
  rw [S.levelReadKernel_apply]
  apply (integrable_map_measure (g := fun r : Euclid dy => ‖r - (gradient S.effectiveValue v + a)‖ ^ 2)
    ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
    (measurable_id.neg.add measurable_const).aemeasurable).mpr
  simpa only [Function.comp_def, id_eq, he] using ht

theorem levelReadKernel_error (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (v a : Euclid dy) (u : Euclid dx) :
    (∫ r, ‖r - (gradient S.effectiveValue v + a)‖ ^ 2 ∂S.levelReadKernel K b v a u) ≤
      ℓ ^ 2 * ‖u - S.sliceMin v‖ ^ 2 + σ ^ 2 / b := by
  obtain ⟨hi, hm, hv, hvar⟩ := K.dual_batch_contract (u, v) hb
  have hmoment := second_moment_about_target (fun r : Euclid dy => r)
    (S.gradY u v) (S.gradY (S.sliceMin v) v) hi hm hv
  have hℓ := S.toNCObjective.L_pos
  have hLip := S.toNCObjective.gradY_lip_primal u (S.sliceMin v) v
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ℓ * ‖u - S.sliceMin v‖)).mpr hLip
  rw [mul_pow] at hsq
  rw [S.levelReadKernel_apply, integral_map (φ := fun r : Euclid dy => -r + a)
    (f := fun r : Euclid dy => ‖r - (gradient S.effectiveValue v + a)‖ ^ 2)
    (measurable_id.neg.add measurable_const).aemeasurable
    ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable]
  have he (r : Euclid dy) : ‖(-r + a) - (gradient S.effectiveValue v + a)‖ ^ 2 =
      ‖r - S.gradY (S.sliceMin v) v‖ ^ 2 := by
    rw [S.true_effective_gradient, effectiveGradient]
    congr 1
    rw [show (-r + a) - (-S.gradY (S.sliceMin v) v + a) = -(r - S.gradY (S.sliceMin v) v) by abel,
      norm_neg]
  simp_rw [he]
  rw [hmoment]
  linarith

def levelKernel (K : FreshOracle S.toNCObjective σ) (b n : ℕ) (v a : Euclid dy) :
    Kernel (Euclid dx) (Euclid dy) := S.levelReadKernel K b v a ∘ₖ S.fastRunKernel K b v n

instance levelKernel_markov (K : FreshOracle S.toNCObjective σ) (b n : ℕ) (v a : Euclid dy) :
    IsMarkovKernel (S.levelKernel K b n v a) := by unfold levelKernel; infer_instance

theorem levelKernel_square_integrable (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (n : ℕ) (v a : Euclid dy) (u : Euclid dx) :
    Integrable (fun r => ‖r - (gradient S.effectiveValue v + a)‖ ^ 2) (S.levelKernel K b n v a u) := by
  have hf : StronglyMeasurable (fun r : Euclid dy => ‖r - (gradient S.effectiveValue v + a)‖ ^ 2) :=
    ((continuous_id.sub continuous_const).norm.pow 2).stronglyMeasurable
  have hu := S.fastRunKernel_square_integrable K hb v n u
  have henv : Integrable (fun w => ℓ ^ 2 * ‖w - S.sliceMin v‖ ^ 2 + σ ^ 2 / b)
      (S.fastRunKernel K b v n u) := (hu.const_mul _).add (integrable_const _)
  have hmean : Integrable (fun w => ∫ r, ‖r - (gradient S.effectiveValue v + a)‖ ^ 2
      ∂S.levelReadKernel K b v a w) (S.fastRunKernel K b v n u) := by
    apply henv.mono' hf.integral_kernel.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
      exact S.levelReadKernel_error K hb v a w)
  unfold levelKernel
  apply (ProbabilityTheory.integrable_comp_iff hf.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (S.levelReadKernel_square_integrable K hb v a), ?_⟩
  simpa only [Real.norm_eq_abs, abs_sq] using hmean

theorem levelKernel_integrable (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (n : ℕ) (v a : Euclid dy) (u : Euclid dx) : Integrable id (S.levelKernel K b n v a u) :=
  integrable_of_centered_square measurable_id.aestronglyMeasurable
    (gradient S.effectiveValue v + a) (S.levelKernel_square_integrable K hb n v a u)

theorem levelKernel_error (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (hα : α ≤ ℓ) (n : ℕ) (v a : Euclid dy) (u : Euclid dx) :
    (∫ r, ‖r - (gradient S.effectiveValue v + a)‖ ^ 2 ∂S.levelKernel K b n v a u) ≤
      ℓ ^ 2 * (1 - α / ℓ) ^ n * ‖u - S.sliceMin v‖ ^ 2 +
        (ℓ / α + 1) * σ ^ 2 / b := by
  have hrun := S.fastRunKernel_error_floor K hb hα v n u
  have hrunInt := S.fastRunKernel_square_integrable K hb v n u
  have hlevel := S.levelKernel_square_integrable K hb n v a u
  change Integrable _ ((S.levelReadKernel K b v a ∘ₖ S.fastRunKernel K b v n) u) at hlevel
  have henv : Integrable (fun w => ℓ ^ 2 * ‖w - S.sliceMin v‖ ^ 2 + σ ^ 2 / b)
      (S.fastRunKernel K b v n u) := (hrunInt.const_mul _).add (integrable_const _)
  have hi := integral_mono hlevel.integral_comp henv (S.levelReadKernel_error K hb v a)
  rw [integral_add (hrunInt.const_mul _) (integrable_const _), integral_const_mul] at hi
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
  unfold levelKernel
  rw [Kernel.integral_comp hlevel]
  have hr := mul_le_mul_of_nonneg_left hrun (sq_nonneg ℓ)
  have he : ℓ ^ 2 * (σ ^ 2 / (α * ℓ * b)) + σ ^ 2 / b = (ℓ / α + 1) * σ ^ 2 / b := by
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
    field_simp [ne_of_gt S.toNCObjective.L_pos, ne_of_gt S.α_pos, hb0]
    ring
  calc
    _ ≤ ℓ ^ 2 * ((1 - α / ℓ) ^ n * ‖u - S.sliceMin v‖ ^ 2 + σ ^ 2 / (α * ℓ * b)) + σ ^ 2 / b := by
      linarith
    _ = _ := by rw [mul_add, add_assoc, he]; ring

end SCObjective
end FreshGradientMinimax
