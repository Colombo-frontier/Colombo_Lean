import RandomizedFO2003.CascadeSpace
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod

namespace RandomizedFO2003.Cascade

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem block_energy_sum {N : ℕ} (x : BlockProduct N E) : ∑ i, ‖x i‖ ^ 2 = ‖x‖ ^ 2 :=
  (PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => E) x).symm

theorem blockProjection_norm_le (N : ℕ) (i : Fin N) : ‖blockProjection (E := E) N i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using block_norm_le x i

/-- Coordinates on one edge; its product norm is bounded by the Euclidean
block norm. Every block is used by at most two such projections. -/
noncomputable def edgeProjection (N : ℕ) (j : Fin N) : BlockProduct (N + 1) E →L[ℝ] E × E :=
  (blockProjection (N + 1) j.castSucc).prod (blockProjection (N + 1) j.succ)

@[simp] theorem edgeProjection_apply {N : ℕ} (j : Fin N) (x : BlockProduct (N + 1) E) :
    edgeProjection N j x = (x j.castSucc, x j.succ) := rfl

theorem edgeProjection_apply_norm_le {N : ℕ} (j : Fin N) (x : BlockProduct (N + 1) E) :
    ‖edgeProjection N j x‖ ≤ ‖x‖ := by
  rw [edgeProjection_apply, Prod.norm_def]
  exact max_le (block_norm_le x j.castSucc) (block_norm_le x j.succ)

theorem edgeProjection_norm_le (N : ℕ) (j : Fin N) : ‖edgeProjection (E := E) N j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using edgeProjection_apply_norm_le j x

theorem edgeProjection_norm_sq_le {N : ℕ} (j : Fin N) (x : BlockProduct (N + 1) E) :
    ‖edgeProjection N j x‖ ^ 2 ≤ ‖x j.castSucc‖ ^ 2 + ‖x j.succ‖ ^ 2 := by
  rw [edgeProjection_apply, Prod.norm_def]
  rcases le_total ‖x j.castSucc‖ ‖x j.succ‖ with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- The exact bounded-incidence input for global derivative estimates.
The constant two is independent of the number and dimension of blocks. -/
theorem edge_energy_sum_le {N : ℕ} (x : BlockProduct (N + 1) E) :
    ∑ j : Fin N, ‖edgeProjection N j x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
  have hleft : ∑ j : Fin N, ‖x j.castSucc‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← block_energy_sum x, Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hright : ∑ j : Fin N, ‖x j.succ‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← block_energy_sum x, Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg _)
  calc
    _ ≤ ∑ j : Fin N, (‖x j.castSucc‖ ^ 2 + ‖x j.succ‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => edgeProjection_norm_sq_le j x)
    _ = (∑ j : Fin N, ‖x j.castSucc‖ ^ 2) + ∑ j : Fin N, ‖x j.succ‖ ^ 2 := Finset.sum_add_distrib
    _ ≤ 2 * ‖x‖ ^ 2 := by linarith

end RandomizedFO2003.Cascade
