import NCBall.Probability
import Mathlib.MeasureTheory.Measure.Prod

/-! # Extracting a fixed instance while retaining all algorithm randomness -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

theorem exists_good_hard_fiber {U Z : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    (μ : Measure U) (ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (good : Set U) (hg : MeasurableSet good) (success : Set (U × Z)) (hs : MeasurableSet success)
    (hgood : (7 / 8 : ℝ≥0∞) ≤ μ good) (hsuccess : (μ.prod ν) success ≤ 1 / 4) :
    ∃ u ∈ good, ν (Prod.mk u ⁻¹' success) < 1 / 2 := by
  classical
  by_contra h
  push_neg at h
  have hpoint (u : U) : good.indicator (fun _ => (1 / 2 : ℝ≥0∞)) u ≤
      ν (Prod.mk u ⁻¹' success) := by
    by_cases hu : u ∈ good
    · simpa only [indicator_of_mem hu] using h u hu
    · simp only [indicator_of_not_mem hu, zero_le]
  have hlow : (1 / 2 : ℝ≥0∞) * μ good ≤ (μ.prod ν) success := by
    rw [Measure.prod_apply hs]
    calc
      (1 / 2 : ℝ≥0∞) * μ good = ∫⁻ u, good.indicator (fun _ => (1 / 2 : ℝ≥0∞)) u ∂μ := by
        rw [lintegral_indicator hg, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := lintegral_mono hpoint
  have hbad := (mul_le_mul_left' hgood (1 / 2 : ℝ≥0∞)).trans (hlow.trans hsuccess)
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ⊤) hbad
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div] at hr

end NCBall
