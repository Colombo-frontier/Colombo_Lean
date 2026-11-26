import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
The event argument in `thm:spectral-estimation`. This module proves the
probability-theoretic consequence of a conditional low-event estimate.
It does not establish the Gaussian core or either hard-edge estimate.
-/

namespace Matvec
open MeasureTheory Set

/-- The sharp scalar minimax step in the spectral estimation proof. -/
theorem separation_arithmetic {f q pLow pHigh : ℝ}
    (hp : 0 ≤ pLow) (hlow : pLow * q ≤ f) (hhigh : pHigh - q ≤ f) :
    pLow * pHigh / (1 + pLow) ≤ f := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + pLow)).2
  nlinarith [mul_le_mul_of_nonneg_left hhigh hp]

/-- A low event with mass at least `pLow` on every relevant transcript event,
and a separated unconditional high event, force estimation error. The
conditional probability input is expressed as its integrated event bound. -/
theorem spectral_failure_of_event_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s estimate : Ω → ℝ) (low high threshold pLow pHigh : ℝ)
    (hp : 0 ≤ pLow) (hsepLow : 2 * low < threshold)
    (hsepHigh : threshold ≤ high / 2)
    (hlow : pLow * μ.real {ω | threshold ≤ estimate ω} ≤
      μ.real ({ω | threshold ≤ estimate ω} ∩ {ω | s ω ≤ low}))
    (hhigh : pHigh ≤ μ.real {ω | high ≤ s ω}) :
    pLow * pHigh / (1 + pLow) ≤
      μ.real {ω | estimate ω ∉ Set.Icc (s ω / 2) (2 * s ω)} := by
  let E := {ω | threshold ≤ estimate ω}
  let Fail := {ω | estimate ω ∉ Set.Icc (s ω / 2) (2 * s ω)}
  have hlowSub : E ∩ {ω | s ω ≤ low} ⊆ Fail := by
    intro ω hω hgood
    have hupper := hgood.2
    change threshold ≤ estimate ω ∧ s ω ≤ low at hω
    linarith [hω.1, hω.2]
  have hhighSub : {ω | high ≤ s ω} ⊆ Fail ∪ E := by
    intro ω hω
    change high ≤ s ω at hω
    by_cases he : ω ∈ E
    · exact Or.inr he
    · left
      have he' : estimate ω < threshold := lt_of_not_ge he
      intro hgood
      linarith [hgood.1]
  apply separation_arithmetic hp
  · exact hlow.trans (measureReal_mono hlowSub)
  · have h := hhigh.trans ((measureReal_mono hhighSub).trans
        (measureReal_union_le Fail E))
    linarith

theorem separation_constant_pos {pLow pHigh : ℝ}
    (hlow : 0 < pLow) (hhigh : 0 < pHigh) :
    0 < pLow * pHigh / (1 + pLow) := by positivity

end Matvec
