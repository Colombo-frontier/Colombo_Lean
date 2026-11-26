import MatchingBounds1005.Model
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-! The exact equivalence between the pointwise initial-gap condition and
the manuscript's finite-infimum formulation. -/
namespace MatchingBounds1005.Model

theorem pointwise_gap_iff_infimum {E : Type*} (f : E → ℝ) (x₀ : E) (Δ : ℝ) :
    (∀ x, f x₀ - f x ≤ Δ) ↔
      BddBelow (Set.range f) ∧ f x₀ - sInf (Set.range f) ≤ Δ := by
  constructor
  · intro h
    have hb : BddBelow (Set.range f) := by
      refine ⟨f x₀ - Δ, ?_⟩
      rintro y ⟨x, rfl⟩
      linarith [h x]
    have hi : f x₀ - Δ ≤ sInf (Set.range f) := by
      apply le_csInf (s := Set.range f) ⟨f x₀, ⟨x₀, rfl⟩⟩
      rintro y ⟨x, rfl⟩
      linarith [h x]
    exact ⟨hb, by linarith⟩
  · rintro ⟨hb, h⟩ x
    have hi : sInf (Set.range f) ≤ f x := csInf_le hb ⟨x, rfl⟩
    linarith

theorem gap_iff_infimum {d : ℕ} (f : Space d → ℝ) :
    (∀ x, f 0 - f x ≤ 1) ↔
      BddBelow (Set.range f) ∧ f 0 - sInf (Set.range f) ≤ 1 :=
  pointwise_gap_iff_infimum f 0 1

theorem inFunctionClass_infimum_gap {d p : ℕ} {f : Space d → ℝ}
    (hf : InFunctionClass p f) : f 0 - sInf (Set.range f) ≤ 1 :=
  ((gap_iff_infimum f).mp hf.2.1).2

end MatchingBounds1005.Model
