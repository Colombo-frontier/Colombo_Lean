import Bilevel.VariableDraws
import Bilevel.BatchOracle

/-! Actual fresh finite sample means on a common stream space, with a concrete
natural call count selected to meet any positive RMS target. -/

noncomputable section
open MeasureTheory

namespace Bilevel.FreshOracle.Oracle

variable {Query Seed Seed' E : Type*}
  [MeasurableSpace Query] [MeasurableSpace Seed] [MeasurableSpace Seed']
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Seed} {ν' : Measure Seed'} [IsProbabilityMeasure ν]
  {σ : ℝ} (O : FreshOracle.Oracle (Query := Query) (E := E) ν σ)

def pullbackSeed (T : Seed' → Seed) (hT : MeasurePreserving T ν' ν) :
    FreshOracle.Oracle (Query := Query) (E := E) ν' σ where
  truth := O.truth
  sample q s := O.sample q (T s)
  truth_measurable := O.truth_measurable
  sample_measurable := O.sample_measurable.comp (measurable_fst.prodMk (hT.measurable.comp measurable_snd))
  square_integrable q := (hT.integrable_comp (O.square_integrable q).aestronglyMeasurable).mpr
    (O.square_integrable q)
  mean q := by
    rw [FreshPullback.integral_pullback hT (fun s => O.sample q s - O.truth q)
      ((O.error_measurable.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)]
    exact O.mean q
  variance q := by
    rw [FreshPullback.integral_pullback hT (fun s => ‖O.sample q s - O.truth q‖ ^ 2)
      (((O.error_measurable.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable).norm.pow 2)]
    exact O.variance q

end Bilevel.FreshOracle.Oracle

namespace Bilevel.FreshBatchKernel

def count (σ radius : ℝ) : ℕ := max 1 ⌈σ ^ 2 / radius ^ 2⌉₊

theorem count_pos (σ radius : ℝ) : 0 < count σ radius :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem variance_bound (σ : ℝ) {radius : ℝ} (hr : 0 < radius) :
    σ ^ 2 / (count σ radius : ℝ) ≤ radius ^ 2 := by
  have hc : σ ^ 2 / radius ^ 2 ≤ (count σ radius : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hm := (div_le_iff₀ (sq_pos_of_pos hr)).mp hc
  exact (div_le_iff₀ (Nat.cast_pos.mpr (count_pos σ radius))).mpr (by nlinarith)

theorem count_le (σ radius : ℝ) : (count σ radius : ℝ) ≤ 1 + σ ^ 2 / radius ^ 2 := by
  have hx : 0 ≤ σ ^ 2 / radius ^ 2 := by positivity
  have hc := (Nat.ceil_lt_add_one hx).le
  unfold count
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith
  · linarith

variable {Query Seed E : Type*} [MeasurableSpace Query] [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Seed} [IsProbabilityMeasure ν] {σ : ℝ}
  (O : FreshOracle.Oracle (Query := Query) (E := E) ν σ)

def oracle (radius : ℝ) (hr : 0 < radius) :
    FreshOracle.Oracle (Query := Query) (E := E) (IndependentStream.law ν) radius := by
  let B := (BatchOracle.oracle O (count σ radius) (count_pos σ radius)).pullbackSeed
    (IndependentStream.project (count σ radius)) (IndependentStream.project_preserves ν _)
  refine {
    truth := B.truth
    sample := B.sample
    truth_measurable := B.truth_measurable
    sample_measurable := B.sample_measurable
    square_integrable := B.square_integrable
    mean := B.mean
    variance := ?_ }
  intro q
  have h := B.variance q
  have he : (σ / Real.sqrt (count σ radius)) ^ 2 = σ ^ 2 / (count σ radius : ℝ) := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [he] at h
  exact h.trans (variance_bound σ hr)

end Bilevel.FreshBatchKernel
