import SampleReuse.StoppedDriftCharging
import SampleReuse.TreeEstimator
import Mathlib.MeasureTheory.Function.Floor

/-! Actual integer batch costs, charging the root once and both endpoints of
each selected edge. Ceiling overhead is charged only on selected edges. -/

open MeasureTheory Filter SecondOrder
open scoped BigOperators InnerProductSpace Classical

namespace SampleReuse
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_batchSize {weight : Ω → ℝ} (hw : Integrable weight μ)
    {scale cap : ℝ} (hs : 0 ≤ scale) (hw0 : ∀ w, 0 ≤ weight w) (hcap : ∀ w, weight w ≤ cap) :
    Integrable (fun w => (batchSize scale (weight w) : ℝ)) μ := by
  have hnat : AEMeasurable (fun w => batchSize scale (weight w)) μ := by
    exact aemeasurable_const.max
      (Nat.measurable_ceil.comp_aemeasurable (aemeasurable_const.mul hw.aemeasurable))
  have hreal : AEMeasurable (fun w => (batchSize scale (weight w) : ℝ)) μ :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp_aemeasurable hnat
  apply (integrable_const (1 + scale * cap)).mono' hreal.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact (batchSize_upper hs (hw0 w)).trans (by gcongr; exact hcap w)

theorem integrable_selected_card {ι : Type*} [Fintype ι] (selected : Ω → ι → Prop)
    (hsel : ∀ i, MeasurableSet {w | selected w i}) :
    Integrable (fun w => ((Finset.univ.filter (selected w)).card : ℝ)) μ := by
  have hi (i : ι) : Integrable (fun w => if selected w i then (1 : ℝ) else 0) μ := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ)).indicator (hsel i)
  have he (w : Ω) : ((Finset.univ.filter (selected w)).card : ℝ) =
      ∑ i : ι, if selected w i then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [he]
  exact integrable_finset_sum Finset.univ (fun i _ => hi i)

/-- An expected-cost bound for the literal integer `treeQueryCost`, without
postulating the bound or assuming integrability of the rounded batches. -/
theorem integral_treeQueryCost {ι : Type*} [Fintype ι]
    (selected : Ω → ι → Prop) (hsel : ∀ i, MeasurableSet {w | selected w i})
    (weight : ι → Ω → ℝ) (hi : ∀ i, Integrable (weight i) μ)
    {scale rootWeight cap : ℝ} (hs : 0 ≤ scale) (hr : 0 ≤ rootWeight)
    (hw0 : ∀ i w, 0 ≤ weight i w) (hcap : ∀ i w, weight i w ≤ cap) :
    Integrable (fun w => (treeQueryCost (Finset.univ.filter (selected w)) scale rootWeight
      (fun i => weight i w) : ℝ)) μ ∧
    (∫ w, (treeQueryCost (Finset.univ.filter (selected w)) scale rootWeight
      (fun i => weight i w) : ℝ) ∂μ) ≤
      1 + 2 * (∫ w, ((Finset.univ.filter (selected w)).card : ℝ) ∂μ) +
        scale * (rootWeight + 2 * (∫ w, ∑ i, if selected w i then weight i w else 0 ∂μ)) := by
  have hbatch (i : ι) := integrable_batchSize (hi i) hs (hw0 i) (hcap i)
  have hsb (i : ι) : Integrable (fun w => if selected w i then
      (batchSize scale (weight i w) : ℝ) else 0) μ := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using (hbatch i).indicator (hsel i)
  have hcost : Integrable (fun w => (treeQueryCost (Finset.univ.filter (selected w))
      scale rootWeight (fun i => weight i w) : ℝ)) μ := by
    have hh := (integrable_const (batchSize scale rootWeight : ℝ)).add
      ((integrable_finset_sum Finset.univ (fun i _ => hsb i)).const_mul 2)
    simpa [treeQueryCost, Finset.sum_filter] using hh
  have hsw (i : ι) : Integrable (fun w => if selected w i then weight i w else 0) μ := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using (hi i).indicator (hsel i)
  have hW := integrable_finset_sum Finset.univ (fun i _ => hsw i)
  have hC := integrable_selected_card (μ := μ) selected hsel
  refine ⟨hcost, ?_⟩
  have hb := integral_mono hcost
    (((integrable_const (1 : ℝ)).add (hC.const_mul 2)).add
      (((integrable_const rootWeight).add (hW.const_mul 2)).const_mul scale))
    (fun w => (show (treeQueryCost (Finset.univ.filter (selected w)) scale rootWeight
      (fun i => weight i w) : ℝ) ≤
      1 + 2 * ((Finset.univ.filter (selected w)).card : ℝ) +
        scale * (rootWeight + 2 * ∑ i, if selected w i then weight i w else 0) by
        simpa only [Finset.sum_filter] using treeQueryCost_upper
          (Finset.univ.filter (selected w)) (fun i => weight i w) hs hr (fun i _ => hw0 i w)))
  simp only [Pi.add_apply] at hb
  have hf : Integrable (fun w => 1 + 2 * ((Finset.univ.filter (selected w)).card : ℝ)) μ :=
    (integrable_const (1 : ℝ)).add (hC.const_mul 2)
  have hg : Integrable (fun w => scale * (rootWeight +
      2 * ∑ i, if selected w i then weight i w else 0)) μ :=
    ((integrable_const rootWeight).add (hW.const_mul 2)).const_mul scale
  rw [integral_add hf hg,
    integral_add (integrable_const (1 : ℝ)) (hC.const_mul 2), integral_const_mul,
    integral_const_mul, integral_add (integrable_const rootWeight) (hW.const_mul 2),
    integral_const_mul] at hb
  simpa using hb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The explicit stochastic sampling cost at bounded stopping checkpoints.
The selector can retain exactly the manuscript's binary-ancestor edges.
The remaining sampler coupling is that this selector records actual edges. -/
theorem stopped_treeQueryCost (T M depth : ℕ) (τ : ℕ → Ω → ℕ)
    (hτmono : ∀ w, Monotone (fun j => τ j w)) (hcap : ∀ w, τ M w ≤ T)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ ‹MeasurableSpace Ω›) (hmono : Monotone past)
    (hτ : ∀ j k, MeasurableSet[past k] {w | τ j w ≤ k})
    (x : Ω → ℕ → E) (a z : Fin T → Ω → E)
    (hx : ∀ w k, x w (k.val + 1) - x w k.val = a k w + z k w)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, MemLp (z k) 2 μ)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j.val] (z i) μ)
    (hzero : ∀ j, μ[z j | past j.val] =ᵐ[μ] (fun _ => 0))
    (selected : Ω → completedNodes depth M → Prop)
    (hselected : ∀ i, MeasurableSet {w | selected w i})
    {σ L scale : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) (hs : 0 ≤ scale) :
    (∫ w, (treeQueryCost (Finset.univ.filter (selected w)) scale (σ ^ 2)
      (fun i => min (σ ^ 2)
        (L ^ 2 * ‖x w (τ (nodeRight i.val) w) - x w (τ (nodeLeft i.val) w)‖ ^ 2)) : ℝ) ∂μ) ≤
      1 + 2 * (∫ w, ((Finset.univ.filter (selected w)).card : ℝ) ∂μ) +
        scale * (σ ^ 2 + 4 * (depth : ℝ) *
          (σ * L * (∫ w, ∑ k, ‖a k w‖ ∂μ) + L ^ 2 * (∫ w, ∑ k, ‖z k w‖ ^ 2 ∂μ))) := by
  let weight (i : completedNodes depth M) (w : Ω) := min (σ ^ 2)
    (L ^ 2 * ‖x w (τ (nodeRight i.val) w) - x w (τ (nodeLeft i.val) w)‖ ^ 2)
  have hi (i : completedNodes depth M) : Integrable (weight i) μ :=
    (integral_stopped_interval (τ (nodeLeft i.val)) (τ (nodeRight i.val))
      (fun w => hτmono w (nodeLeft_lt_right i.val).le)
      (fun w => (hτmono w ((mem_completedNodes i.val).mp i.property)).trans (hcap w))
      past hp hmono (hτ _) (hτ _) x a z hx ha hz hadapt hzero hσ hL).1
  have hcost := (integral_treeQueryCost selected hselected weight hi hs (sq_nonneg σ)
    (fun i w => le_min (sq_nonneg _) (by positivity))
    (fun _ _ => min_le_left _ _)).2
  have hb := selected_stopped_checkpoint_charging T M depth τ hτmono hcap past hp hmono hτ
    x a z hx ha hz hadapt hzero selected hselected hσ hL
  have hmul := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * scale)
  dsimp only [weight] at hcost
  nlinarith

end
end SampleReuse
