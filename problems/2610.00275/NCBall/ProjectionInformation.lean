import NCBall.Geometry
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # What reusing one sample handle can reveal

These are deterministic linear-algebra facts. They do not assert independence
of Gaussian innovations after an adaptive transcript.
-/

noncomputable section
open scoped InnerProductSpace
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two possible noisy sample vectors agreeing on every queried direction
agree on the entire span. A repeated direction adds no new scalar information. -/
theorem measurements_determine_span {ι : Type*} (a : ι → E) (v w : E)
    (h : ∀ i, ⟪v, a i⟫_ℝ = ⟪w, a i⟫_ℝ) {b : E}
    (hb : b ∈ Submodule.span ℝ (Set.range a)) : ⟪v, b⟫_ℝ = ⟪w, b⟫_ℝ := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
  · rintro _ ⟨i, rfl⟩
    exact h i
  · simp
  · intro x y _ _ hx hy
    simp only [inner_add_right, hx, hy]
  · intro r x _ hx
    simp only [inner_smul_right, hx]

/-- q scalar observations reveal a subspace of dimension at most q. -/
theorem observed_span_rank_le {q : ℕ} (a : Fin q → E) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range a)) ≤ q := by
  simpa using finrank_range_le_card (R := ℝ) a

end NCBall
