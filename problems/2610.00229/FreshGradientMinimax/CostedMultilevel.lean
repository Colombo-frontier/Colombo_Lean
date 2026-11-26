import FreshGradientMinimax.MultilevelKernel

/-! A cost tag retained alongside the multilevel output. Its first marginal
is the estimator already analysed, and its expected tag is the exact finite
weighted sum of the three sampled level costs. EstimatorImplementation
connects the standalone estimator to original oracle transcripts; the full
adaptive solver's implementation is still separate. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Q R : Type*} [MeasurableSpace Q] [MeasurableSpace R]

def taggedKernel (L : Kernel Q R) (c : ℕ) : Kernel Q (R × ℕ) :=
  L.map (fun r => (r, c))

instance taggedKernel_markov (L : Kernel Q R) [IsMarkovKernel L] (c : ℕ) :
    IsMarkovKernel (taggedKernel L c) :=
  Kernel.IsMarkovKernel.map _ (measurable_id.prodMk measurable_const)

theorem taggedKernel_first (L : Kernel Q R) (c : ℕ) : (taggedKernel L c).map Prod.fst = L := by
  apply Kernel.ext
  intro q
  rw [Kernel.map_apply _ measurable_fst, taggedKernel,
    Kernel.map_apply (f := fun r : R => (r, c)) _ (measurable_id.prodMk measurable_const),
    Measure.map_map (f := fun r : R => (r, c)) measurable_fst (measurable_id.prodMk measurable_const)]
  change Measure.map id (L q) = L q
  exact Measure.map_id

theorem taggedKernel_cost_integrable (L : Kernel Q R) [IsMarkovKernel L] (c : ℕ) (q : Q) :
    Integrable (fun z : R × ℕ => (z.2 : ℝ)) (taggedKernel L c q) := by
  rw [taggedKernel, Kernel.map_apply (f := fun r : R => (r, c)) _ (measurable_id.prodMk measurable_const)]
  apply (integrable_map_measure (μ := L q) (g := fun z : R × ℕ => (z.2 : ℝ)) (f := fun r : R => (r, c))
    (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_snd).aestronglyMeasurable)
    (measurable_id.prodMk measurable_const).aemeasurable).mpr
  exact integrable_const (μ := L q) (c : ℝ)

theorem taggedKernel_mean_cost (L : Kernel Q R) [IsMarkovKernel L] (c : ℕ) (q : Q) :
    (∫ z, (z.2 : ℝ) ∂taggedKernel L c q) = c := by
  rw [taggedKernel, Kernel.map_apply (f := fun r : R => (r, c)) _ (measurable_id.prodMk measurable_const),
    integral_map (f := fun z : R × ℕ => (z.2 : ℝ)) (φ := fun r : R => (r, c))
      (measurable_id.prodMk measurable_const).aemeasurable
      (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_snd).aestronglyMeasurable)]
  simp

variable {d : ℕ}

def costedMultilevelKernel (L : ℕ → Kernel Q (Euclid d)) (c : ℕ → ℕ) (K : ℕ) :
    Kernel Q (Euclid d × ℕ) :=
  if K = 0 then taggedKernel (L 0) (c 0) else
    finiteMixtureKernel (levelProbability K) (fun j =>
      taggedKernel (independentCorrectionKernel (L 0) (L (j + 1)) (L j) (levelProbability K j))
        (c 0 + c (j + 1) + c j)) K

instance costedMultilevelKernel_markov (L : ℕ → Kernel Q (Euclid d))
    [∀ j, IsMarkovKernel (L j)] (c : ℕ → ℕ) (K : ℕ) :
    IsMarkovKernel (costedMultilevelKernel L c K) := by
  by_cases hK : K = 0
  · rw [costedMultilevelKernel, if_pos hK]; infer_instance
  · rw [costedMultilevelKernel, if_neg hK]
    exact finiteMixtureKernel_markov _ _ _
      (fun j _ => (level_probability_pos (Nat.pos_of_ne_zero hK) j).le)
      (level_probabilities_sum (Nat.pos_of_ne_zero hK))

theorem costedMultilevelKernel_first (L : ℕ → Kernel Q (Euclid d)) (c : ℕ → ℕ) (K : ℕ) :
    (costedMultilevelKernel L c K).map Prod.fst = multilevelKernel L K := by
  by_cases hK : K = 0
  · rw [costedMultilevelKernel, multilevelKernel, if_pos hK, if_pos hK, taggedKernel_first]
  · rw [costedMultilevelKernel, multilevelKernel, if_neg hK, if_neg hK,
      finiteMixtureKernel_map _ _ _ _ measurable_fst]
    simp_rw [taggedKernel_first]

theorem costedMultilevelKernel_cost_integrable (L : ℕ → Kernel Q (Euclid d))
    [∀ j, IsMarkovKernel (L j)] (c : ℕ → ℕ) (K : ℕ) (q : Q) :
    Integrable (fun z : Euclid d × ℕ => (z.2 : ℝ)) (costedMultilevelKernel L c K q) := by
  by_cases hK : K = 0
  · rw [costedMultilevelKernel, if_pos hK]
    exact taggedKernel_cost_integrable _ _ _
  · rw [costedMultilevelKernel, if_neg hK]
    exact finiteMixtureKernel_integrable _ _ _ _ _ (fun _ _ => taggedKernel_cost_integrable _ _ _)

theorem costedMultilevelKernel_mean_cost (L : ℕ → Kernel Q (Euclid d))
    [∀ j, IsMarkovKernel (L j)] (c : ℕ → ℕ) (K : ℕ) (q : Q) :
    (∫ z, (z.2 : ℝ) ∂costedMultilevelKernel L c K q) =
      (c 0 : ℝ) + ∑ j ∈ Finset.range K, levelProbability K j * ((c (j + 1) : ℝ) + c j) := by
  by_cases hK : K = 0
  · rw [costedMultilevelKernel, if_pos hK, taggedKernel_mean_cost]
    simp [hK]
  · have hKpos := Nat.pos_of_ne_zero hK
    rw [costedMultilevelKernel, if_neg hK,
      finiteMixtureKernel_integral _ _ _ _ _ (fun j _ => (level_probability_pos hKpos j).le)
        (fun _ _ => taggedKernel_cost_integrable _ _ _)]
    simp_rw [taggedKernel_mean_cost, Nat.cast_add, smul_eq_mul]
    calc
      _ = ∑ j ∈ Finset.range K,
          (levelProbability K j * (c 0 : ℝ) + levelProbability K j * ((c (j + 1) : ℝ) + c j)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, level_probabilities_sum hKpos, one_mul]

end FreshGradientMinimax
