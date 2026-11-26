import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! Probability-to-risk and fixed-frame extraction for nonnegative integrals.
These lemmas remain valid for algorithms with nonintegrable output norms. -/
noncomputable section
namespace Smoothness2601.LowerRisk
open MeasureTheory
open scoped ENNReal

theorem good_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad saturated : Set Ω) (hb : MeasurableSet bad) (hs : MeasurableSet saturated)
    (hbad : μ.real bad ≤ 1/8) (hsat : μ.real saturated ≤ 1/8) :
    (3/4 : ℝ) ≤ μ.real (bad ∪ saturated)ᶜ := by
  rw [measureReal_compl (hb.union hs),measureReal_univ_eq_one]
  have hu := measureReal_union_le bad saturated (μ := μ)
  linarith

theorem risk_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad saturated : Set Ω) (hb : MeasurableSet bad) (hs : MeasurableSet saturated)
    (hbad : μ.real bad ≤ 1/8) (hsat : μ.real saturated ≤ 1/8)
    (risk : Ω → ℝ≥0∞) (margin : ℝ≥0∞)
    (hmargin : ∀ᵐ ω ∂μ, ω ∉ bad → ω ∉ saturated → margin ≤ risk ω) :
    margin*ENNReal.ofReal (3/4 : ℝ) ≤ ∫⁻ ω, risk ω ∂μ := by
  let good := (bad ∪ saturated)ᶜ
  have hg : MeasurableSet good := (hb.union hs).compl
  have hprob : ENNReal.ofReal (3/4 : ℝ) ≤ μ good := by
    have hp := ENNReal.ofReal_le_ofReal (good_probability μ bad saturated hb hs hbad hsat)
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hp
  have hi : good.indicator (fun _ => margin) ≤ᵐ[μ] risk := by
    filter_upwards [hmargin] with ω hω
    by_cases hωg : ω ∈ good
    · rw [Set.indicator_of_mem hωg]
      exact hω (fun h => hωg (Or.inl h)) (fun h => hωg (Or.inr h))
    · rw [Set.indicator_of_not_mem hωg]
      exact zero_le _
  have hli := lintegral_mono_ae hi
  rw [lintegral_indicator_const hg] at hli
  exact (mul_le_mul_left' hprob margin).trans hli

/-- Tonelli gives a fixed valid frame with large conditional expected norm;
no finiteness or Bochner integrability hypothesis is needed. -/
theorem fixed_frame {Seed Frame : Type*} [MeasurableSpace Seed] [MeasurableSpace Frame]
    (ν : Measure Seed) (μ : Measure Frame) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (valid : Frame → Prop) (hvalid : ∀ᵐ U ∂μ, valid U)
    (risk : Seed × Frame → ℝ≥0∞) (hrisk : Measurable risk) (target : ℝ≥0∞)
    (hmean : target < ∫⁻ p, risk p ∂ν.prod μ) :
    ∃ U, valid U ∧ target < ∫⁻ s, risk (s,U) ∂ν := by
  by_contra hn
  push_neg at hn
  have hi : (∫⁻ U, ∫⁻ s, risk (s,U) ∂ν ∂μ) ≤ target := by
    calc
      _ ≤ ∫⁻ _U, target ∂μ := lintegral_mono_ae (hvalid.mono fun U hU => hn U hU)
      _ = _ := by simp
  rw [lintegral_prod_symm _ hrisk.aemeasurable] at hmean
  exact (not_lt_of_ge hi) hmean

end Smoothness2601.LowerRisk
