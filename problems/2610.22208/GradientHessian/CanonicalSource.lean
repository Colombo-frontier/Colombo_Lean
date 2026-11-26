import GradientHessian.ConditionedSource
import GradientHessian.ReadoutMarks

/-! A fixed marked coordinate subspace for the presampled construction.
The projector and orthonormal columns are explicit, with their actual rank. -/

noncomputable section
namespace GradientHessian.CanonicalSource
open Matrix LowRank

def columns {r d : ℕ} (h : r≤d) : Matrix (Fin d) (Fin r) ℝ :=
  fun i j => if i = Fin.castLE h j then 1 else 0

theorem columns_orthonormal {r d : ℕ} (h : r≤d) : (columns h)ᵀ * columns h = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columns]
  simp [Matrix.one_apply, Finset.sum_ite_eq', Fin.castLE_inj, eq_comm]

def projector {r d : ℕ} (h : r≤d) : Matrix (Fin d) (Fin d) ℝ := columns h * (columns h)ᵀ

theorem projector_orthogonal {r d : ℕ} (h : r≤d) : IsOrthogonalProjector (projector h) := by
  constructor
  · simp [projector, Matrix.transpose_mul]
  · unfold projector
    calc
      (columns h * (columns h)ᵀ) * (columns h * (columns h)ᵀ) =
          columns h * ((columns h)ᵀ * columns h) * (columns h)ᵀ := by simp [Matrix.mul_assoc]
      _ = _ := by rw [columns_orthonormal, Matrix.mul_one]

theorem projector_columns {r d : ℕ} (h : r≤d) : projector h * columns h = columns h := by
  rw [projector, Matrix.mul_assoc, columns_orthonormal, Matrix.mul_one]

theorem columns_rank {r d : ℕ} (h : r≤d) : (columns h).rank = r := by
  apply le_antisymm
  · simpa using (columns h).rank_le_width
  · have hr := Matrix.rank_mul_le_right (columns h)ᵀ (columns h)
    simpa only [columns_orthonormal, Matrix.rank_one, Fintype.card_fin] using hr

theorem projector_rank {r d : ℕ} (h : r≤d) : (projector h).rank = r := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left (columns h) (columns h)ᵀ).trans_eq (columns_rank h)
  · have hr := Matrix.rank_mul_le_left (projector h) (columns h)
    rw [projector_columns, columns_rank] at hr
    exact hr

theorem marked_dimension_le {J r κ : ℕ} (hJ : 1≤J) (hκ : 1≤κ) : r≤(κ*r)*J := by
  calc
    r ≤ κ*r := by simpa using Nat.mul_le_mul_right r hκ
    _ ≤ (κ*r)*J := by simpa using Nat.mul_le_mul_left (κ*r) hJ

theorem conditioned_probability {J r κ : ℕ} (hJ : 4≤J)
    (hr : 1+4096*J^2≤r) (hκ : 18874368≤κ) :
    MeasureTheory.IsProbabilityMeasure (ConditionedSource.sourceLaw (n := (κ*r)*J-κ*r)
      (projector (marked_dimension_le (r := r) (by omega : 1≤J) (by omega : 1≤κ))) J) := by
  exact ConditionedSource.sourceLaw_probability hJ hr hκ rfl rfl _
    (projector_orthogonal _) (projector_rank _)

end GradientHessian.CanonicalSource
