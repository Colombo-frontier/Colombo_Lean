import Matvec.ProductSeparation

/-! Integrating uniform algorithm success over a high-probability input
promise. The promise set itself need not have a separately supplied
measurability proof: the measurable success-probability superlevel set is used. -/
namespace Matvec
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem product_success_of_pointwise {S X : Type*}
    [MeasurableSpace S] [MeasurableSpace X]
    (ν : Measure S) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (F : Set (S × X)) (hF : MeasurableSet F) (Good : Set X)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hGood : 1 - δ ≤ μ.real Good)
    (hsuccess : ∀ x ∈ Good, 1 - ε ≤ ν.real {s | (s, x) ∈ F}) :
    1 - ε - δ ≤ (ν.prod μ).real F := by
  let E := {x : X | 1 - ε ≤ ν.real {s | (s, x) ∈ F}}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_measure_prodMk_right hF).ennreal_toReal
  have hGE : Good ⊆ E := hsuccess
  have hmass : 1 - δ ≤ μ.real E := hGood.trans (measureReal_mono hGE)
  have hint : ENNReal.ofReal (1 - ε) * μ E ≤ (ν.prod μ) F := by
    calc
      _ = ∫⁻ x, E.indicator (fun _ => ENNReal.ofReal (1 - ε)) x ∂μ := by
        rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x, ν ((fun s => (s, x)) ⁻¹' F) ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ E
        · rw [indicator_of_mem hx]
          have h := ENNReal.ofReal_le_ofReal hx
          change ENNReal.ofReal (1 - ε) ≤
            ENNReal.ofReal (ν.real ((fun s => (s, x)) ⁻¹' F)) at h
          rwa [ofReal_measureReal] at h
        · rw [indicator_of_not_mem hx]
          exact zero_le _
      _ = _ := (Measure.prod_apply_symm hF).symm
  have h := ENNReal.toReal_mono (measure_ne_top (ν.prod μ) F) hint
  have hp : 0 ≤ 1 - ε := by linarith
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, measureReal_def] at h
  change (1 - ε) * μ.real E ≤ (ν.prod μ).real F at h
  have hm := mul_le_mul_of_nonneg_left hmass hp
  nlinarith [mul_nonneg hε hδ]

theorem product_failure_of_pointwise {S X : Type*}
    [MeasurableSpace S] [MeasurableSpace X]
    (ν : Measure S) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (F : Set (S × X)) (hF : MeasurableSet F) (Good : Set X)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hGood : 1 - δ ≤ μ.real Good)
    (hsuccess : ∀ x ∈ Good, 1 - ε ≤ ν.real {s | (s, x) ∈ F}) :
    (ν.prod μ).real Fᶜ ≤ ε + δ := by
  have h := product_success_of_pointwise ν μ F hF Good ε δ hε hε1 hδ hGood hsuccess
  rw [measureReal_compl hF]
  simp only [measureReal_univ_eq_one]
  linarith

end
end Matvec
