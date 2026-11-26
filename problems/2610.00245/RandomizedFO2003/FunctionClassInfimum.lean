import RandomizedFO2003.Model
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace RandomizedFO2003.Model

/-- The pairwise initial-gap formulation is exactly the paper's finite
infimum formulation, without assuming that a minimum is attained. -/
theorem pairwise_gap_iff_infimum {X : Type*} (f : X → ℝ) (initial : X) (Δ : ℝ) :
    (∀ x, f initial - f x ≤ Δ) ↔
      BddBelow (Set.range f) ∧ f initial - sInf (Set.range f) ≤ Δ := by
  have hne : (Set.range f).Nonempty := ⟨f initial, Set.mem_range_self initial⟩
  constructor
  · intro h
    have hb : ∀ y ∈ Set.range f, f initial - Δ ≤ y := by
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      linarith [h x]
    exact ⟨⟨f initial - Δ, hb⟩, by linarith [le_csInf hne hb]⟩
  · rintro ⟨hb, hg⟩ x
    have hx := csInf_le hb (Set.mem_range_self x)
    linarith

theorem inFunctionClass_iff_infimum {d : ℕ} (f : Space d → ℝ) (Δ L₁ L₂ : ℝ) :
    InFunctionClass f Δ L₁ L₂ ↔
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ f 0 - sInf (Set.range f) ≤ Δ ∧
        (∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) ∧
        (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ L₂ * ‖x - y‖) := by
  rw [InFunctionClass, pairwise_gap_iff_infimum]
  tauto

end RandomizedFO2003.Model
