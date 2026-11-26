import RandomizedFO2003.OracleMeasurability
import Mathlib.MeasureTheory.Measure.Prod

namespace RandomizedFO2003.Model

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} {Param : Type*} {Seed : Type} [MeasurableSpace Param] [MeasurableSpace Seed]

/-- Probability averaging for the exact algorithm model, allowing a null
set of sampled parameters outside the function class. The distributional
bound remains an explicit hypothesis. -/
theorem exists_hard_sample_of_joint_bound (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2))
    (μ : Measure Param) (ν : Measure Seed) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε Δ L₁ L₂ : ℝ} {T : ℕ} {p q : ℝ≥0∞}
    (hclass : ∀ᵐ x ∂μ, InFunctionClass (f x) Δ L₁ L₂)
    (hpq : p < q) (hbound : (μ.prod ν) (familySuccess A f ε T) ≤ p) :
    ∃ x, InFunctionClass (f x) Δ L₁ L₂ ∧ ν (Success A (f x) ε T) < q := by
  by_contra hn
  push_neg at hn
  have hlo : ∀ᵐ x ∂μ, q ≤ ν (Success A (f x) ε T) := hclass.mono (fun x hx => hn x hx)
  have hmeasure : (μ.prod ν) (familySuccess A f ε T) =
      ∫⁻ x, ν (Success A (f x) ε T) ∂μ := by
    simpa only [familySuccess, Set.preimage_setOf_eq] using
      (Measure.prod_apply (μ := μ) (ν := ν) (measurableSet_familySuccess A f hf ε T))
  have hlow : q ≤ (μ.prod ν) (familySuccess A f ε T) := by
    rw [hmeasure]
    calc
      q = ∫⁻ _x, q ∂μ := by simp
      _ ≤ ∫⁻ x, ν (Success A (f x) ε T) ∂μ := lintegral_mono_ae hlo
  exact (not_le_of_gt hpq) (hlow.trans hbound)

theorem joint_bound_of_seedwise_bound (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2))
    (μ : Measure Param) (ν : Measure Seed) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} {T : ℕ} {p : ℝ≥0∞}
    (hbound : ∀ seed, μ {x | seed ∈ Success A (f x) ε T} ≤ p) :
    (μ.prod ν) (familySuccess A f ε T) ≤ p := by
  rw [Measure.prod_apply_symm (measurableSet_familySuccess A f hf ε T)]
  calc
    _ ≤ ∫⁻ _seed, p ∂ν := lintegral_mono hbound
    _ = p := by simp

/-- The final existential quantifier concerns a genuine function in the
target class and its actual success event, including arbitrary output. -/
theorem exists_hard_function_of_seedwise_bound (A : Algorithm d Seed) (f : Param → Space d → ℝ)
    (hf : Measurable (fun p : Param × Space d => oracle (f p.1) p.2))
    (μ : Measure Param) (ν : Measure Seed) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε Δ L₁ L₂ : ℝ} {T : ℕ} {p : ℝ≥0∞}
    (hclass : ∀ᵐ x ∂μ, InFunctionClass (f x) Δ L₁ L₂)
    (hp : p < (2 / 3 : ℝ≥0∞))
    (hbound : ∀ seed, μ {x | seed ∈ Success A (f x) ε T} ≤ p) :
    ∃ g : Space d → ℝ, InFunctionClass g Δ L₁ L₂ ∧ ν (Success A g ε T) < (2 / 3 : ℝ≥0∞) := by
  obtain ⟨x, hx, hs⟩ := exists_hard_sample_of_joint_bound A f hf μ ν hclass hp
    (joint_bound_of_seedwise_bound A f hf μ ν hbound)
  exact ⟨f x, hx, hs⟩

end RandomizedFO2003.Model
