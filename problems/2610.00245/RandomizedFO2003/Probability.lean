import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace RandomizedFO2003

open MeasureTheory
open scoped ENNReal NNReal

/-- The measurable averaging step of Yao's argument. This is not a construction
of a hard distribution: its uniform deterministic bound is an explicit hypothesis.
`win` may be the indicator of a jointly measurable success event. -/
theorem yao_obstruction
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (μ : Measure Instance) (ν : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (win : Instance → Seed → ℝ≥0∞)
    (hmeas : AEMeasurable (Function.uncurry win) (μ.prod ν))
    (p q : ℝ≥0∞) (hpq : p < q)
    (hdet : ∀ seed, (∫⁻ inst, win inst seed ∂μ) ≤ p) :
    ¬ ∀ inst, q ≤ ∫⁻ seed, win inst seed ∂ν := by
  intro hsuccess
  have hlow : q ≤ ∫⁻ inst, ∫⁻ seed, win inst seed ∂ν ∂μ := by
    calc
      q = ∫⁻ _instance, q ∂μ := by simp
      _ ≤ ∫⁻ inst, ∫⁻ seed, win inst seed ∂ν ∂μ := lintegral_mono hsuccess
  have hupp : (∫⁻ seed, ∫⁻ inst, win inst seed ∂μ ∂ν) ≤ p := by
    calc
      (∫⁻ seed, ∫⁻ inst, win inst seed ∂μ ∂ν) ≤ ∫⁻ _seed, p ∂ν :=
        lintegral_mono hdet
      _ = p := by simp
  rw [lintegral_lintegral_swap hmeas] at hlow
  exact (not_le_of_gt hpq) (hlow.trans hupp)

/-- A uniform distributional success bound below 2/3 rules out a worst-case
2/3 guarantee, without assuming the seed space or inst space is finite. -/
theorem yao_one_third
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (μ : Measure Instance) (ν : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (win : Instance → Seed → ℝ≥0∞)
    (hmeas : AEMeasurable (Function.uncurry win) (μ.prod ν))
    (hdet : ∀ seed, (∫⁻ inst, win inst seed ∂μ) ≤ 1 / 3) :
    ¬ ∀ inst, (2 / 3 : ℝ≥0∞) ≤ ∫⁻ seed, win inst seed ∂ν := by
  apply yao_obstruction μ ν win hmeas (1 / 3) (2 / 3) _ hdet
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num)).mpr
  norm_num

end RandomizedFO2003
