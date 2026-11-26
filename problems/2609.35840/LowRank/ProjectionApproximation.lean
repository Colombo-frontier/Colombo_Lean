import LowRank.FrobeniusCompression
import LowRank.MeasurableRankOne

/-! Frobenius contraction and approximation by a vector block already in
the projected subspace. These estimates turn filtered block constructions
into quantitative distances from a target eigenspace. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem frobeniusSq_eq_trace_right {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    frobeniusSq B = (Bᵀ * B).trace := by
  rw [frobeniusSq_eq_trace, Matrix.trace_mul_comm]

theorem frobeniusSq_neg {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    frobeniusSq (-B) = frobeniusSq B := by
  simp only [frobeniusSq, Matrix.neg_apply, neg_sq]

theorem frobeniusSq_orthogonal_left {a d k : ℕ}
    (V : Matrix (Fin a) (Fin d) ℝ) (hV : Vᵀ * V = 1) (B : Matrix (Fin d) (Fin k) ℝ) :
    frobeniusSq (V * B) = frobeniusSq B := by
  rw [frobeniusSq_eq_trace_right, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Vᵀ V B, hV, Matrix.one_mul, ← frobeniusSq_eq_trace_right]

theorem frobeniusSq_projector_mul_le {d k : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (B : Matrix (Fin d) (Fin k) ℝ) :
    frobeniusSq (P * B) ≤ frobeniusSq B := by
  rw [frobeniusSq_eq_trace, Matrix.transpose_mul, hP.symmetric, frobeniusSq_eq_trace]
  have heq : P * B * (Bᵀ * P) = P * (B * Bᵀ) * P := by simp only [Matrix.mul_assoc]
  rw [heq, trace_compression hP]
  apply projector_trace_mul_le_trace hP
  simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose B

theorem frobeniusSq_residual_le_of_fixed_perturbation {d k : ℕ}
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (T E : Matrix (Fin d) (Fin k) ℝ) (hfix : P * (T + E) = T + E) :
    frobeniusSq ((1 - P) * T) ≤ frobeniusSq E := by
  have hz : (1 - P) * (T + E) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hfix, sub_self]
  rw [Matrix.mul_add] at hz
  have heq : (1 - P) * T = -((1 - P) * E) := eq_neg_of_add_eq_zero_left hz
  rw [heq, frobeniusSq_neg]
  exact frobeniusSq_projector_mul_le hP.complement E

theorem frobeniusSq_diagonal_sandwich_le {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ)
    (left : Fin m → ℝ) (right : Fin k → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hl : ∀ i, |left i| ≤ η) (hr : ∀ j, |right j| ≤ 1) :
    frobeniusSq (diagonal left * B * diagonal right) ≤ η ^ 2 * frobeniusSq B := by
  simp only [frobeniusSq, Matrix.mul_diagonal, Matrix.diagonal_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have habs : |left i * B i j * right j| ≤ η * |B i j| := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (η * |B i j|) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hl i) (abs_nonneg _)) (hr j)
          (abs_nonneg _) (mul_nonneg hη (abs_nonneg _))
      _ = _ := mul_one _
  have hsq := pow_le_pow_left₀ (abs_nonneg (left i * B i j * right j)) habs 2
  simpa only [sq_abs, mul_pow, sq_abs] using hsq

end
end LowRank
