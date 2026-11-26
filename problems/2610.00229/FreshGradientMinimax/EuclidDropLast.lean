import FreshGradientMinimax.EuclidBlockOperator
import FreshGradientMinimax.PathCoordinates

/-! Removing the unused last coordinate and its exact zero-padding adjoint. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def euclidDropLast (m : ℕ) : Euclid (m + 1) →L[ℝ] Euclid m := (pathPadLeft m)†

@[simp]
theorem euclidDropLast_apply {m : ℕ} (x : Euclid (m + 1)) (i : Fin m) :
    euclidDropLast m x i = x i.castSucc := by
  have h := (pathPadLeft m).adjoint_inner_left (EuclideanSpace.single i 1) x
  simpa [euclidDropLast, pathPadLeft_single, EuclideanSpace.inner_single_right] using h

theorem euclidDropLast_adjoint (m : ℕ) : (euclidDropLast m)† = pathPadLeft m :=
  ContinuousLinearMap.adjoint_adjoint _

theorem euclidDropLast_norm {m : ℕ} (x : Euclid (m + 1)) : ‖euclidDropLast m x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclid_norm_sq, euclid_norm_sq x, Fin.sum_univ_castSucc]
  simp only [euclidDropLast_apply]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem euclidDropLast_opNorm (m : ℕ) : ‖euclidDropLast m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => by simpa only [one_mul] using euclidDropLast_norm x)

def interleavedX {k : ℕ} (i : Fin k) : Fin (k * 2 + 1) := (finProdFinEquiv (i, (0 : Fin 2))).castSucc
def interleavedZ {k : ℕ} (i : Fin k) : Fin (k * 2 + 1) := (finProdFinEquiv (i, (1 : Fin 2))).castSucc
def interleavedNextX {k : ℕ} (i : Fin k) : Fin (k * 2 + 1) := (finProdFinEquiv (i, (1 : Fin 2))).succ

theorem interleaved_norm_sq {k : ℕ} (x : Euclid (k * 2 + 1)) :
    ‖x‖ ^ 2 = (∑ i : Fin k, (x (interleavedX i) ^ 2 + x (interleavedZ i) ^ 2)) + x (Fin.last (k * 2)) ^ 2 := by
  rw [euclid_norm_sq, Fin.sum_univ_castSucc, sum_fin_blocks]
  simp only [Fin.sum_univ_two, interleavedX, interleavedZ]

end FreshGradientMinimax
