import LowRank.MatrixOrder
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Trace

/-! For an orthogonal projector, the trace is its actual matrix rank.
This discharges the trace condition when an algorithm promises rank k. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem IsOrthogonalProjector.trace_eq_rank {a : Type*} [Fintype a] [DecidableEq a]
    {P : Matrix a a ℝ} (hP : IsOrthogonalProjector P) : P.trace = (P.rank : ℝ) := by
  have hp : LinearMap.IsProj (LinearMap.range P.mulVecLin) P.mulVecLin := by
    constructor
    · intro x
      exact LinearMap.mem_range_self _ x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      change P *ᵥ (P *ᵥ y) = P *ᵥ y
      rw [Matrix.mulVec_mulVec, hP.idempotent]
  have ht := hp.trace
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ a), LinearMap.toMatrix_eq_toMatrix'] at ht
  change (LinearMap.toMatrix' (Matrix.toLin' P)).trace = (P.rank : ℝ) at ht
  simpa only [LinearMap.toMatrix'_toLin'] using ht

theorem IsOrthogonalProjector.trace_le_of_rank_le {a : Type*} [Fintype a] [DecidableEq a]
    {P : Matrix a a ℝ} (hP : IsOrthogonalProjector P) {k : ℕ} (hk : P.rank ≤ k) : P.trace ≤ (k : ℝ) := by
  rw [hP.trace_eq_rank]
  exact_mod_cast hk

end
end LowRank
