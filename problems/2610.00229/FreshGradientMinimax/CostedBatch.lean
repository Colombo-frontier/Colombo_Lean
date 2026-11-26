import FreshGradientMinimax.BatchKernel
import FreshGradientMinimax.CostedMultilevel

/-! Independent averaging retains every sampled estimator's natural-number
cost. Its output marginal and expected accumulated cost are exact. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def costValue {Y : Type*} (z : Y × ℕ) : ℝ := z.2

theorem costValue_measurable {Y : Type*} [MeasurableSpace Y] : Measurable (costValue (Y := Y)) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_snd

def costedAdd (z : (Euclid d × ℕ) × (Euclid d × ℕ)) : Euclid d × ℕ :=
  (z.1.1 + z.2.1, z.1.2 + z.2.2)

theorem costedAdd_measurable : Measurable (costedAdd (d := d)) :=
  (measurable_fst.fst.add measurable_snd.fst).prodMk (measurable_fst.snd.add measurable_snd.snd)

def costedSumKernel (K : Kernel X (Euclid d × ℕ)) : ℕ → Kernel X (Euclid d × ℕ)
  | 0 => Kernel.deterministic (fun _ => (0, 0)) measurable_const
  | n + 1 => (costedSumKernel K n ×ₖ K).map costedAdd

instance costedSumKernel_markov (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (costedSumKernel K n) := by
  induction n with
  | zero => dsimp [costedSumKernel]; infer_instance
  | succ n ih =>
    letI := ih
    exact Kernel.IsMarkovKernel.map _ costedAdd_measurable

theorem costedSumKernel_first (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K] (n : ℕ) :
    (costedSumKernel K n).map Prod.fst = iidSumKernel (K.map Prod.fst) n := by
  induction n with
  | zero =>
    apply Kernel.ext
    intro x
    simp only [costedSumKernel, iidSumKernel, Kernel.map_apply _ measurable_fst,
      Kernel.deterministic_apply, Measure.map_dirac measurable_fst]
  | succ n ih =>
    rw [costedSumKernel, ← Kernel.map_comp_right _ costedAdd_measurable measurable_fst, iidSumKernel, ← ih,
      Kernel.map_prod_map _ _ measurable_fst measurable_fst,
      ← Kernel.map_comp_right _ (measurable_fst.prodMap measurable_fst) (measurable_fst.add measurable_snd)]
    rfl

theorem costedSumKernel_cost (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K] (x : X)
    (hi : Integrable costValue (K x)) (n : ℕ) :
    Integrable costValue (costedSumKernel K n x) ∧
    (∫ z, costValue z ∂costedSumKernel K n x) = (n : ℝ) * ∫ z, costValue z ∂K x := by
  induction n with
  | zero => simp [costedSumKernel, Kernel.deterministic_apply, costValue, integrable_dirac]
  | succ n ih =>
    have hs : Integrable (fun z : (Euclid d × ℕ) × (Euclid d × ℕ) => costValue z.1 + costValue z.2)
        ((costedSumKernel K n x).prod (K x)) :=
      (integrable_on_product_fst ih.1).add (integrable_on_product_snd hi)
    rw [costedSumKernel, Kernel.map_apply _ costedAdd_measurable, Kernel.prod_apply]
    constructor
    · apply (integrable_map_measure (g := costValue) costValue_measurable.aestronglyMeasurable
        costedAdd_measurable.aemeasurable).mpr
      simpa only [Function.comp_def, costValue, costedAdd, Nat.cast_add] using hs
    · rw [integral_map (f := costValue) (φ := costedAdd) costedAdd_measurable.aemeasurable
        costValue_measurable.aestronglyMeasurable]
      simp only [costValue, costedAdd, Nat.cast_add]
      have h := independent_sum_mean ih.1 hi
      rw [ih.2] at h
      simpa only [costValue, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

def costedBatchKernel (K : Kernel X (Euclid d × ℕ)) (b : ℕ) : Kernel X (Euclid d × ℕ) :=
  (costedSumKernel K b).map (fun z => ((b : ℝ)⁻¹ • z.1, z.2))

instance costedBatchKernel_markov (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K] (b : ℕ) :
    IsMarkovKernel (costedBatchKernel K b) :=
  Kernel.IsMarkovKernel.map _ ((measurable_const.smul measurable_fst).prodMk measurable_snd)

theorem costedBatchKernel_first (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K] (b : ℕ) :
    (costedBatchKernel K b).map Prod.fst = batchKernel (K.map Prod.fst) b := by
  rw [costedBatchKernel, ← Kernel.map_comp_right _ ((measurable_const.smul measurable_fst).prodMk measurable_snd)
    measurable_fst, batchKernel, ← costedSumKernel_first K b,
    ← Kernel.map_comp_right _ (g := fun r : Euclid d => (b : ℝ)⁻¹ • r)
      measurable_fst (measurable_const.smul measurable_id)]
  rfl

theorem costedBatchKernel_cost (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K] (x : X)
    (hi : Integrable costValue (K x)) (b : ℕ) :
    Integrable costValue (costedBatchKernel K b x) ∧
    (∫ z, costValue z ∂costedBatchKernel K b x) = (b : ℝ) * ∫ z, costValue z ∂K x := by
  have h := costedSumKernel_cost K x hi b
  rw [costedBatchKernel, Kernel.map_apply _ ((measurable_const.smul measurable_fst).prodMk measurable_snd)]
  constructor
  · exact (integrable_map_measure (g := costValue) costValue_measurable.aestronglyMeasurable
      ((measurable_const.smul measurable_fst).prodMk measurable_snd).aemeasurable).mpr h.1
  · rw [integral_map (f := costValue) (φ := fun z : Euclid d × ℕ => ((b : ℝ)⁻¹ • z.1, z.2))
      ((measurable_const.smul measurable_fst).prodMk measurable_snd).aemeasurable
      costValue_measurable.aestronglyMeasurable]
    exact h.2

end FreshGradientMinimax
