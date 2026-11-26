import Mathlib.MeasureTheory.Measure.Real

/-! A quantile minimax definition with dependent sample spaces. The lower-bound
bridge uses a strict failure probability and handles atoms by testing every
strictly smaller threshold. This file contains no optimization-rate premise. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeavyTail

section
variable {Algorithm Instance : Type*} {Ω : Instance → Algorithm → Type*}
variable [∀ i a, MeasurableSpace (Ω i a)]

def uniformErrorThresholds
    (P : ∀ i a, Measure (Ω i a)) (loss : ∀ i a, Ω i a → ℝ)
    (δ : ℝ) (a : Algorithm) : Set ℝ≥0∞ :=
  {ε | ∀ i, (P i a).real {ω | ε < ENNReal.ofReal (loss i a ω)} ≤ δ}

def minimaxErrorQuantile
    (P : ∀ i a, Measure (Ω i a)) (loss : ∀ i a, Ω i a → ℝ)
    (δ : ℝ) : ℝ≥0∞ :=
  ⨅ a, sInf (uniformErrorThresholds P loss δ a)

theorem minimaxErrorQuantile_upper
    (P : ∀ i a, Measure (Ω i a)) (loss : ∀ i a, Ω i a → ℝ)
    (δ : ℝ) (a : Algorithm) (ε : ℝ≥0∞)
    (h : ∀ i, (P i a).real {ω | ε < ENNReal.ofReal (loss i a ω)} ≤ δ) :
    minimaxErrorQuantile P loss δ ≤ ε := by
  exact iInf_le_of_le a (sInf_le h)

/-- A non-strict loss event with probability strictly greater than δ certifies
the full quantile lower bound, including at atoms of the loss distribution. -/
theorem minimaxErrorQuantile_lower
    (P : ∀ i a, Measure (Ω i a)) [∀ i a, IsFiniteMeasure (P i a)]
    (loss : ∀ i a, Ω i a → ℝ) (δ α : ℝ)
    (h : ∀ a, ∃ i, δ < (P i a).real {ω | α ≤ loss i a ω}) :
    ENNReal.ofReal α ≤ minimaxErrorQuantile P loss δ := by
  apply le_iInf
  intro a
  apply le_sInf
  intro ε hε
  by_contra hn
  have hlt : ε < ENNReal.ofReal α := lt_of_not_ge hn
  obtain ⟨i, hi⟩ := h a
  have hsub : {ω | α ≤ loss i a ω} ⊆ {ω | ε < ENNReal.ofReal (loss i a ω)} := by
    intro ω hω
    exact hlt.trans_le (ENNReal.ofReal_le_ofReal hω)
  exact (not_lt_of_ge (hε i)) (hi.trans_le (measureReal_mono hsub))

/-- Enlarging the instance class can only increase the minimax quantile. -/
theorem minimaxErrorQuantile_instance_lower
    (P : ∀ i a, Measure (Ω i a)) (loss : ∀ i a, Ω i a → ℝ)
    (δ : ℝ) (J : Type*) (embed : J → Instance) :
    minimaxErrorQuantile (fun j a ↦ P (embed j) a)
      (fun j a ↦ loss (embed j) a) δ ≤ minimaxErrorQuantile P loss δ := by
  apply iInf_mono
  intro a
  apply sInf_le_sInf
  intro ε hε j
  exact hε (embed j)

end
end HeavyTail
