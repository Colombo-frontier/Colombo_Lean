import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-! Arbitrarily small positive scalar perturbations make any visible square
pivot invertible. The choice is pointwise; no measurable perturbation selector
is needed for subsequent pointwise conditional-probability estimates. -/

namespace Matvec
open Matrix Polynomial
open scoped Matrix
noncomputable section

theorem eval_neg_charpoly_shift {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (δ : ℝ) :
    (-A).charpoly.eval δ = (A + δ • 1).det := by
  change (Polynomial.evalRingHom δ) ((-A).charmatrix.det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.charmatrix, Matrix.scalar, Matrix.one_apply, add_comm]
  · simp [Matrix.charmatrix, Matrix.scalar, Matrix.one_apply, hij]

theorem exists_small_invertible_pivot_shift {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ (A + δ • 1).det ≠ 0 := by
  have hf : Set.Finite {δ : ℝ | Polynomial.IsRoot (-A).charpoly δ} :=
    Polynomial.finite_setOf_isRoot (-A).charpoly_monic.ne_zero
  obtain ⟨δ, hδ, hn⟩ := (Set.Ioo_infinite hε).exists_not_mem_finite hf
  refine ⟨δ, hδ.1, hδ.2, ?_⟩
  intro hz
  apply hn
  change (-A).charpoly.eval δ = 0
  rw [eval_neg_charpoly_shift, hz]

theorem exists_small_pivot_with_inverse {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      (A + δ • 1) * (A + δ • 1)⁻¹ = 1 ∧ (A + δ • 1)⁻¹ * (A + δ • 1) = 1 := by
  obtain ⟨δ, hp, hs, hd⟩ := exists_small_invertible_pivot_shift A hε
  exact ⟨δ, hp, hs, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)⟩

end
end Matvec
