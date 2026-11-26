import UpperGhostFinite

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
namespace Task006.Full

theorem ghostProcess_disagreement_probability_le {E B : Type*}
    [MeasurableSpace E] [MeasurableSpace B] [MeasurableEq E]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (hpos : ∀ x, μ (G x) ≠ 0)
    (step : E × B → E) (hstep : Measurable step) (x0 : E) {q : ℝ} (hq : 0 ≤ q)
    (hbad : ∀ x, μ (G x)ᶜ ≤ ENNReal.ofReal q) (n : ℕ) :
    (ghostProcessLaw μ G hG hpos step hstep x0 n).real {j | j.1.1 ≠ j.1.2} ≤ n * q := by
  have hm := ghostProcess_agreement μ G hG hpos step hstep x0 n
  have hsub : ∀ᵐ j ∂ghostProcessLaw μ G hG hpos step hstep x0 n,
      j ∈ {j | j.1.1 ≠ j.1.2} → j ∈ ghostFailed := by
    filter_upwards [hm] with j hj
    intro hn
    have hf : j.2 ≠ false := fun hfalse => hn (hj hfalse)
    cases hflag : j.2 with
    | false => exact False.elim (hf hflag)
    | true => exact hflag
  have hp := ENNReal.toReal_mono (measure_ne_top _ ghostFailed) (measure_mono_ae hsub)
  exact hp.trans (ghostProcess_failure_real_le μ G hG hpos step hstep x0 hq hbad n)

#print axioms ghostProcess_disagreement_probability_le
end Task006.Full
