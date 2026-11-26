import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! A literal counterexample to the appendix's claim that a compact coefficient
ball can contain all polynomial minimizers for all probability measures.
For the Dirac measure at 1, every p_K(x)=1+K(x-1) has zero inverse-approximation
loss. This does not disprove the minimax identity or the finite-design lemma. -/

namespace RandomizedFO2003.MinimaxCompactness

open Polynomial

noncomputable def affineFamily (K : ℝ) : Polynomial ℝ := C (1 - K) + C K * X
noncomputable def singletonLoss (p : Polynomial ℝ) : ℝ := (1 - p.eval 1) ^ 2

theorem affine_degree (K : ℝ) : (affineFamily K).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_C_mul_le K X).trans (by simp)

theorem affine_slope (K : ℝ) : (affineFamily K).coeff 1 = K := by
  simp [affineFamily, Polynomial.coeff_one]

theorem affine_zero_loss (K : ℝ) : singletonLoss (affineFamily K) = 0 := by
  simp [singletonLoss, affineFamily]

theorem affine_minimizer (K : ℝ) (p : Polynomial ℝ) :
    singletonLoss (affineFamily K) ≤ singletonLoss p := by
  rw [affine_zero_loss]
  exact sq_nonneg _

theorem minimizers_have_unbounded_coefficients :
    ∀ B : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ 1 ∧
      (∀ q : Polynomial ℝ, singletonLoss p ≤ singletonLoss q) ∧
      B < |p.coeff 1| := by
  intro B
  refine ⟨affineFamily (|B| + 1), affine_degree _, affine_minimizer _, ?_⟩
  rw [affine_slope, abs_of_pos (by positivity : 0 < |B| + 1)]
  linarith [le_abs_self B]

theorem no_bounded_ball_contains_all_minimizers :
    ¬ ∃ B : ℝ, ∀ p : Polynomial ℝ, p.natDegree ≤ 1 →
      (∀ q : Polynomial ℝ, singletonLoss p ≤ singletonLoss q) → |p.coeff 1| ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨p, hp, hmin, hlarge⟩ := minimizers_have_unbounded_coefficients B
  exact (not_le_of_gt hlarge) (hB p hp hmin)

end RandomizedFO2003.MinimaxCompactness
