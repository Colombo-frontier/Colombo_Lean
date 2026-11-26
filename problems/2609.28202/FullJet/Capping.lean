import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory Set

namespace FullJet

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Markov with a freely chosen target failure probability. -/
theorem markov_rescaled {f : Ω → ℝ} (hf : Integrable f P)
    (hpos : ∀ ω, 0 ≤ f ω) (Q η : ℝ) (hQ : 0 < Q) (hη : 0 < η)
    (hmean : ∫ ω, f ω ∂P ≤ Q) :
    P.real {ω | Q / η ≤ f ω} ≤ η := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hpos) hf (Q / η)
  have hmul : Q / η * P.real {ω | Q / η ≤ f ω} ≤ Q := h.trans hmean
  have hscale : Q / η * η = Q := div_mul_cancel₀ _ hη.ne'
  exact (mul_le_mul_left (div_pos hQ hη)).mp (hmul.trans_eq hscale.symm)

/-- Corrected expected-cost conversion. The budget is `2 Q / δ` and the
gradient tolerance is `2 ε / δ`, giving failure at most `δ` for any `δ > 0`.
This supplies the confidence missing from the source's factors of four. -/
theorem capping_failure_le {τ g : Ω → ℝ} (hτ : Integrable τ P) (hg : Integrable g P)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (Q ε δ : ℝ) (hQ : 0 < Q) (hε : 0 < ε) (hδ : 0 < δ)
    (hcost : ∫ ω, τ ω ∂P ≤ Q) (hgrad : ∫ ω, g ω ∂P ≤ ε) :
    P.real {ω | Q / (δ / 2) ≤ τ ω ∨ ε / (δ / 2) ≤ g ω} ≤ δ := by
  have hc := markov_rescaled hτ hτ0 Q (δ / 2) hQ (by positivity) hcost
  have hg' := markov_rescaled hg hg0 ε (δ / 2) hε (by positivity) hgrad
  have hu := measureReal_union_le (μ := P)
    {ω | Q / (δ / 2) ≤ τ ω} {ω | ε / (δ / 2) ≤ g ω}
  change P.real {ω | Q / (δ / 2) ≤ τ ω ∨ ε / (δ / 2) ≤ g ω} ≤ _ at hu
  linarith

end FullJet
