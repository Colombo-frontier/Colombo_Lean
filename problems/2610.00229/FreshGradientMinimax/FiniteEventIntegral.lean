import FreshGradientMinimax.FiniteBadEvents
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Conversion between finite indicator averages and actual seed probabilities. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators

theorem truthValue_indicator {Ω : Type*} (S : Set Ω) :
    (fun x => truthValue (x ∈ S)) = S.indicator (fun _ => (1 : ℝ)) := by
  classical
  funext x
  simp only [truthValue, Set.indicator_apply]

theorem truthValue_integrable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    {S : Set Ω} (hS : MeasurableSet S) : Integrable (fun x => truthValue (x ∈ S)) ν := by
  rw [truthValue_indicator]
  exact (integrable_const 1).indicator hS

theorem integral_truthValue {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {S : Set Ω} (hS : MeasurableSet S) : (∫ x, truthValue (x ∈ S) ∂ν) = ν.real S := by
  rw [truthValue_indicator, integral_indicator hS]
  simp

theorem integrable_finite_average {I Ω : Type*} [Fintype I] [MeasurableSpace Ω] {ν : Measure Ω}
    (f : I → Ω → ℝ) (hf : ∀ i, Integrable (f i) ν) :
    Integrable (fun x => 𝔼 i, f i x) ν := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  exact (integrable_finset_sum _ (fun i _ => hf i)).div_const _

theorem integral_finite_average {I Ω : Type*} [Fintype I] [MeasurableSpace Ω] {ν : Measure Ω}
    (f : I → Ω → ℝ) (hf : ∀ i, Integrable (f i) ν) :
    (∫ x, 𝔼 i, f i x ∂ν) = 𝔼 i, ∫ x, f i x ∂ν := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [integral_div, integral_finset_sum _ (fun i _ => hf i)]

end FreshGradientMinimax
