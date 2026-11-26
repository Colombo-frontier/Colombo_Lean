import Matvec.ModelGapBridge
import Matvec.DilationSpectrum

/-! Coordinate geometry of an actual Euclidean operator-norm source promise,
and admissibility of the ball embedding in the quantified algorithm model. -/
namespace Matvec
open Matrix
open scoped Matrix BigOperators
noncomputable section

def euclideanMatrixMap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

theorem matrix_column_sq_le_opNorm {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (C : ℝ) (hC : 0 ≤ C) (hA : ‖euclideanMatrixMap A‖ ≤ C)
    (j : κ) : ∑ i, A i j ^ 2 ≤ C ^ 2 := by
  classical
  let x : EuclideanSpace ℝ κ := (WithLp.equiv 2 (κ → ℝ)).symm (Pi.single j 1)
  have hx : ‖x‖ = 1 := by
    have hs := euclidean_norm_sq x
    change ‖x‖ ^ 2 = ∑ i, (Pi.single j (1 : ℝ) i) ^ 2 at hs
    simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
    nlinarith [norm_nonneg x]
  have hnorm : ‖euclideanMatrixMap A x‖ ≤ C := by
    have h := (euclideanMatrixMap A).le_opNorm x
    rw [hx, mul_one] at h
    exact h.trans hA
  have hs := (sq_le_sq₀ (norm_nonneg _) hC).mpr hnorm
  rw [euclidean_norm_sq] at hs
  have heq (i : ι) : euclideanMatrixMap A x i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    simp
  simpa only [heq] using hs

theorem symmetric_row_sq_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.transpose = H) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ‖euclideanMatrixMap H‖ ≤ C) (i : ι) : ∑ j, H i j ^ 2 ≤ C ^ 2 := by
  have h := matrix_column_sq_le_opNorm H C hC hnorm i
  have heq (j : ι) : H j i = H i j := congrFun (congrFun hH i) j
  simpa only [heq] using h

theorem source_expansion_squares {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℝ)
    (hH : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖) :
    ∀ v : ι → ℝ, ∑ i, v i ^ 2 ≤ ∑ i, (H *ᵥ v) i ^ 2 := by
  intro v
  let z : EuclideanSpace ℝ ι := (WithLp.equiv 2 (ι → ℝ)).symm v
  have h := (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (Matrix.toEuclideanLin H z))).mpr (hH z)
  rw [euclidean_norm_sq, euclidean_norm_sq] at h
  exact h

theorem euclidean_unit_sq {ι : Type*} [Fintype ι] (b : EuclideanSpace ℝ ι)
    (hb : ‖b‖ ≤ 1) : ∑ i, b i ^ 2 ≤ 1 := by
  have h := (sq_le_sq₀ (norm_nonneg b) (by norm_num : (0 : ℝ) ≤ 1)).mpr hb
  simpa only [euclidean_norm_sq, one_pow] using h

theorem modelBallMatrix_admissible {d m n : ℕ} (hd : 0 < d)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.transpose = H)
    (b : EuclideanSpace ℝ (Fin d)) (hb : ‖b‖ ≤ 1)
    (κ α β : ℝ) (hκ : 1 ≤ κ) (hβ : β = 1 / (4 * κ))
    (hα : α = β / (8 * Real.sqrt d)) (hnorm : ‖euclideanMatrixMap H‖ ≤ κ)
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit)) :
    Admissible .ballSimplex (modelBallMatrix H b α β er ec) := by
  have hrows := BallNormalization.ballMatrix_normalized (by omega : 1 ≤ d)
    H (fun i => b i) hκ hβ hα
    (symmetric_row_sq_le_opNorm H hH κ (by linarith) hnorm) (euclidean_unit_sq b hb)
  intro i
  change (∑ j, ((-ballMatrix H (fun i => b i) α β) (er i) (ec j)) ^ 2) ≤ 1
  rw [ec.sum_comp (fun j => ((-ballMatrix H (fun i => b i) α β) (er i) j) ^ 2)]
  exact (hrows (er i)).2.le

end
end Matvec
