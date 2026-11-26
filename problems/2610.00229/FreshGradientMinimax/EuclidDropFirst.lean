import FreshGradientMinimax.EuclidDropLast

/-! The shifted, disjoint pairs used by the accelerated nonlinear term. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def euclidDropFirst (m : ℕ) : Euclid (m + 1) →L[ℝ] Euclid m := (pathPadRight m)†

@[simp]
theorem euclidDropFirst_apply {m : ℕ} (x : Euclid (m + 1)) (i : Fin m) :
    euclidDropFirst m x i = x i.succ := by
  have h := (pathPadRight m).adjoint_inner_left (EuclideanSpace.single i 1) x
  simpa [euclidDropFirst, pathPadRight_single, EuclideanSpace.inner_single_right] using h

theorem euclidDropFirst_adjoint (m : ℕ) : (euclidDropFirst m)† = pathPadRight m :=
  ContinuousLinearMap.adjoint_adjoint _

theorem euclidDropFirst_norm {m : ℕ} (x : Euclid (m + 1)) : ‖euclidDropFirst m x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclid_norm_sq, euclid_norm_sq x, Fin.sum_univ_succ]
  simp only [euclidDropFirst_apply]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem euclidDropFirst_opNorm (m : ℕ) : ‖euclidDropFirst m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => by simpa only [one_mul] using euclidDropFirst_norm x)

theorem interleavedZ_eq_succ {k : ℕ} (i : Fin k) :
    interleavedZ i = (finProdFinEquiv (i, (0 : Fin 2))).succ := by
  apply Fin.ext
  simp [interleavedZ, finProdFinEquiv, Nat.add_comm]

@[simp]
theorem euclidDropFirst_block_zero {k : ℕ} (i : Fin k) (q : Euclid (k * 2 + 1)) :
    euclidBlock i (euclidDropFirst (k * 2) q) (0 : Fin 2) = q (interleavedZ i) := by
  rw [euclidBlock_apply, euclidDropFirst_apply, interleavedZ_eq_succ]

@[simp]
theorem euclidDropFirst_block_one {k : ℕ} (i : Fin k) (q : Euclid (k * 2 + 1)) :
    euclidBlock i (euclidDropFirst (k * 2) q) (1 : Fin 2) = q (interleavedNextX i) := by
  rw [euclidBlock_apply, euclidDropFirst_apply]
  rfl

end FreshGradientMinimax
