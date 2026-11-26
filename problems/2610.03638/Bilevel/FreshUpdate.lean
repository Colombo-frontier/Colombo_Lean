import Bilevel.FreshOracle

/-! One actual fresh noisy update on a product probability space. -/

noncomputable section
open MeasureTheory

namespace Bilevel.FreshOracle.Oracle

variable {Query Seed E : Type*} [MeasurableSpace Query] [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Seed} [IsProbabilityMeasure ν] {σ : ℝ}
  (O : FreshOracle.Oracle (Query := Query) (E := E) ν σ)

/-- Freeze or transform the query without changing the original samples. -/
def requery {Query' : Type*} [MeasurableSpace Query'] (q : Query' → Query) (hq : Measurable q) :
    FreshOracle.Oracle (Query := Query') (E := E) ν σ where
  truth := O.truth ∘ q
  sample := fun x => O.sample (q x)
  truth_measurable := O.truth_measurable.comp hq
  sample_measurable := O.sample_measurable.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  square_integrable := fun x => O.square_integrable (q x)
  mean := fun x => O.mean (q x)
  variance := fun x => O.variance (q x)

/-- A known frozen linear tilt adds the same deterministic gradient to each
sample and its mean, preserving the original variance exactly. -/
def shift (a : E) : FreshOracle.Oracle (Query := Query) (E := E) ν σ where
  truth := fun q => O.truth q + a
  sample := fun q s => O.sample q s + a
  truth_measurable := O.truth_measurable.add_const a
  sample_measurable := O.sample_measurable.add_const a
  square_integrable := fun q => by simpa only [add_sub_add_right_eq_sub] using O.square_integrable q
  mean := fun q => by simpa only [add_sub_add_right_eq_sub] using O.mean q
  variance := fun q => by simpa only [add_sub_add_right_eq_sub] using O.variance q

variable {Past : Type*} [MeasurableSpace Past] {μ : Measure Past} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem fst_preserves : MeasurePreserving (Prod.fst : Past × Seed → Past) (μ.prod ν) μ :=
  ⟨measurable_fst, by simp only [Measure.map_fst_prod, measure_univ, one_smul]⟩

omit [CompleteSpace E] in
theorem update_memLp (q : Past → Query) (hq : Measurable q) (d : Past → E)
    (hd : MemLp d 2 μ) (η : ℝ) :
    MemLp (fun z : Past × Seed => d z.1 - η • O.adaptiveError q z) 2 (μ.prod ν) :=
  (hd.comp_measurePreserving fst_preserves).sub ((O.adaptiveError_memLp q hq).const_smul η)

omit [CompleteSpace E] in
theorem update_square_integrable (q : Past → Query) (hq : Measurable q) (d : Past → E)
    (hd : MemLp d 2 μ) (η : ℝ) :
    Integrable (fun z : Past × Seed => ‖d z.1 - η • O.adaptiveError q z‖ ^ 2) (μ.prod ν) :=
  (memLp_two_iff_integrable_sq_norm (O.update_memLp q hq d hd η).aestronglyMeasurable).mp
    (O.update_memLp q hq d hd η)

theorem update_risk_bound (q : Past → Query) (hq : Measurable q) (d : Past → E)
    (hd : MemLp d 2 μ) (η : ℝ) :
    (∫ z : Past × Seed, ‖d z.1 - η • O.adaptiveError q z‖ ^ 2 ∂μ.prod ν) ≤
      (∫ z, ‖d z‖ ^ 2 ∂μ) + η ^ 2 * σ ^ 2 := by
  have hu := O.update_square_integrable q hq d hd η
  have hd2 := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hp (z : Past) : (∫ s, ‖d z - η • O.adaptiveError q (z, s)‖ ^ 2 ∂ν) ≤
      ‖d z‖ ^ 2 + η ^ 2 * σ ^ 2 := by
    change (∫ s, ‖d z - η • O.error (q z) s‖ ^ 2 ∂ν) ≤ _
    rw [StochasticInner.fixed_step_identity (d z) (O.error (q z)) η
      (O.error_integrable (q z)) (O.square_integrable (q z)) (O.mean (q z))]
    exact add_le_add_left (mul_le_mul_of_nonneg_left (O.variance (q z)) (sq_nonneg η)) _
  rw [integral_prod _ hu]
  have h := integral_mono hu.integral_prod_left (hd2.add (integrable_const (η ^ 2 * σ ^ 2))) hp
  simpa only [Pi.add_apply, integral_add hd2 (integrable_const (η ^ 2 * σ ^ 2)), integral_const,
    measureReal_univ_eq_one, one_smul] using h

end Bilevel.FreshOracle.Oracle
