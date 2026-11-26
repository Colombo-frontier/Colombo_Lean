import Matvec.SpectralSeparation
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Fubini integration of a uniform conditional low event, and the resulting
estimation failure bound on an actual product probability space. -/
namespace Matvec
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem product_low_event {S D : Type*} [MeasurableSpace S] [MeasurableSpace D]
    (ν : Measure S) (ρ : Measure D) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (score : S × D → ℝ) (hscore : Measurable score) (L p : ℝ) (hp : 0 ≤ p)
    (hlow : ∀ s, p ≤ ρ.real {d | score (s, d) ≤ L})
    (E : Set S) (hE : MeasurableSet E) :
    p * ν.real E ≤ (ν.prod ρ).real ((Prod.fst ⁻¹' E) ∩ {x | score x ≤ L}) := by
  let F := (Prod.fst ⁻¹' E) ∩ {x : S × D | score x ≤ L}
  have hF : MeasurableSet F := (hE.preimage measurable_fst).inter
    (measurableSet_le hscore measurable_const)
  have hp' (s : S) : ENNReal.ofReal p ≤ ρ {d | score (s, d) ≤ L} := by
    have h := ENNReal.ofReal_le_ofReal (hlow s)
    rwa [ofReal_measureReal] at h
  have hint : ENNReal.ofReal p * ν E ≤ (ν.prod ρ) F := by
    calc
      _ = ∫⁻ s, E.indicator (fun _ => ENNReal.ofReal p) s ∂ν := by
        rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ s, ρ (Prod.mk s ⁻¹' F) ∂ν := by
        apply lintegral_mono
        intro s
        by_cases hs : s ∈ E
        · rw [indicator_of_mem hs]
          have heq : Prod.mk s ⁻¹' F = {d | score (s, d) ≤ L} := by
            ext d; simp [F, hs]
          change ENNReal.ofReal p ≤ ρ (Prod.mk s ⁻¹' F)
          rw [heq]
          exact hp' s
        · rw [indicator_of_not_mem hs]
          exact zero_le _
      _ = _ := (Measure.prod_apply hF).symm
  have h := ENNReal.toReal_mono (measure_ne_top (ν.prod ρ) F) hint
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, measureReal_def] using h

theorem product_spectral_failure {S D : Type*} [MeasurableSpace S] [MeasurableSpace D]
    (ν : Measure S) (ρ : Measure D) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (score : S × D → ℝ) (estimate : S → ℝ)
    (hscore : Measurable score) (hestimate : Measurable estimate)
    (low high threshold pLow pHigh : ℝ) (hp : 0 ≤ pLow)
    (hsepLow : 2 * low < threshold) (hsepHigh : threshold ≤ high / 2)
    (hlow : ∀ s, pLow ≤ ρ.real {d | score (s, d) ≤ low})
    (hhigh : pHigh ≤ (ν.prod ρ).real {x | high ≤ score x}) :
    pLow * pHigh / (1 + pLow) ≤ (ν.prod ρ).real
      {x | estimate x.1 ∉ Set.Icc (score x / 2) (2 * score x)} := by
  apply spectral_failure_of_event_bounds (ν.prod ρ) score (fun x => estimate x.1)
    low high threshold pLow pHigh hp hsepLow hsepHigh _ hhigh
  have hE : MeasurableSet {s | threshold ≤ estimate s} :=
    measurableSet_le measurable_const hestimate
  have h := product_low_event ν ρ score hscore low pLow hp hlow _ hE
  have heq : (ν.prod ρ).real {x : S × D | threshold ≤ estimate x.1} =
      ν.real {s | threshold ≤ estimate s} := by
    have hset : {x : S × D | threshold ≤ estimate x.1} =
        {s | threshold ≤ estimate s} ×ˢ Set.univ := by ext x; simp
    rw [hset, measureReal_prod_prod, measureReal_univ_eq_one, mul_one]
  rw [heq]
  exact h

theorem preserving_real_preimage {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} {T : Ω → X} (hT : MeasurePreserving T μ ν)
    (E : Set X) (hE : MeasurableSet E) : ν.real E = μ.real (T ⁻¹' E) := by
  rw [← hT.map_eq]
  exact map_measureReal_apply hT.measurable hE

/-- Transfer the product-space impossibility theorem back through an actual
measure-preserving adaptive exposure process. -/
theorem preserving_product_spectral_failure {Ω S D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace D]
    (μ : Measure Ω) (ν : Measure S) (ρ : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (T : Ω → S × D) (hT : MeasurePreserving T μ (ν.prod ρ))
    (score : S × D → ℝ) (estimate : S → ℝ)
    (hscore : Measurable score) (hestimate : Measurable estimate)
    (low high threshold pLow pHigh : ℝ) (hp : 0 ≤ pLow)
    (hsepLow : 2 * low < threshold) (hsepHigh : threshold ≤ high / 2)
    (hlow : ∀ s, pLow ≤ ρ.real {d | score (s, d) ≤ low})
    (hhigh : pHigh ≤ μ.real {x | high ≤ score (T x)}) :
    pLow * pHigh / (1 + pLow) ≤ μ.real
      {x | estimate (T x).1 ∉ Set.Icc (score (T x) / 2) (2 * score (T x))} := by
  have hhigh' : pHigh ≤ (ν.prod ρ).real {x | high ≤ score x} := by
    rw [preserving_real_preimage hT _ (measurableSet_le measurable_const hscore)]
    exact hhigh
  have h := product_spectral_failure ν ρ score estimate hscore hestimate
    low high threshold pLow pHigh hp hsepLow hsepHigh hlow hhigh'
  have hF : MeasurableSet {x : S × D |
      estimate x.1 ∉ Set.Icc (score x / 2) (2 * score x)} := by
    change MeasurableSet ({x | score x / 2 ≤ estimate x.1} ∩
      {x | estimate x.1 ≤ 2 * score x})ᶜ
    exact ((measurableSet_le (hscore.div_const 2) (hestimate.comp measurable_fst)).inter
      (measurableSet_le (hestimate.comp measurable_fst) (hscore.const_mul 2))).compl
  rw [preserving_real_preimage hT _ hF] at h
  exact h

end
end Matvec
