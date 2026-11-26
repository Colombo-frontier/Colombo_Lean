import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! The good/bad event expectation conversion in the capped upper algorithm.
The loss can be the finite uniform-output average conditional on a complete
oracle history. Its construction and the failure probability remain separate.
-/
noncomputable section
open MeasureTheory
namespace Bilevel.CachedExpectedAccuracy

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- A global cap supplies integrability even on the failure event. -/
theorem expectation_from_cap (loss : Ω → ℝ) (bad : Set Ω) (hbad : MeasurableSet bad)
    (hm : AEStronglyMeasurable loss ν) {ε G δ : ℝ}
    (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hloss : ∀ ω, 0 ≤ loss ω) (hcap : ∀ ω, loss ω ≤ G)
    (hgood : ∀ ω ∉ bad, loss ω ≤ ε / 2) (hprob : ν.real bad ≤ δ) :
    Integrable loss ν ∧ (∫ ω, loss ω ∂ν) ≤ ε / 2 + δ * G := by
  classical
  have hi : Integrable loss ν := (integrable_const G).mono' hm
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_of_nonneg (hloss ω)]
      exact hcap ω))
  have hdom (ω : Ω) : loss ω ≤ ε / 2 + bad.indicator (fun _ => G) ω := by
    by_cases hb : ω ∈ bad
    · simp only [Set.indicator_of_mem hb]
      linarith [hcap ω]
    · simpa [Set.indicator_of_not_mem hb] using hgood ω hb
  have hind : Integrable (bad.indicator (fun _ => G)) ν :=
    (integrable_const G).indicator hbad
  have hh := integral_mono hi ((integrable_const (ε/2)).add hind) hdom
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const (ε/2)) hind,
    integral_const, integral_indicator_const G hbad] at hh
  simp only [measureReal_univ_eq_one, one_smul, smul_eq_mul, one_mul] at hh
  exact ⟨hi, hh.trans (add_le_add_left (mul_le_mul_of_nonneg_right hprob hG) _)⟩

/-- The source chooses a smaller failure budget (epsilon/16); epsilon/2
already suffices for the desired expected gradient-norm criterion. -/
theorem accuracy_from_cap (loss : Ω → ℝ) (bad : Set Ω) (hbad : MeasurableSet bad)
    (hm : AEStronglyMeasurable loss ν) {ε G δ : ℝ}
    (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hloss : ∀ ω, 0 ≤ loss ω) (hcap : ∀ ω, loss ω ≤ G)
    (hgood : ∀ ω ∉ bad, loss ω ≤ ε / 2) (hprob : ν.real bad ≤ δ)
    (hbudget : δ * G ≤ ε / 2) :
    Integrable loss ν ∧ (∫ ω, loss ω ∂ν) ≤ ε := by
  obtain ⟨hi, hb⟩ := expectation_from_cap loss bad hbad hm hε hG hloss hcap hgood hprob
  exact ⟨hi, by linarith⟩

end Bilevel.CachedExpectedAccuracy
