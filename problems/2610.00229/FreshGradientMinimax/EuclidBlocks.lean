import FreshGradientMinimax.SparsePairNorm
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Two finite Euclidean blocks, with exact inner product and norm formulas. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def euclidAppend {n m : ℕ} (x : Euclid n) (y : Euclid m) : Euclid (n + m) :=
  (WithLp.equiv 2 _).symm (Fin.addCases (fun i => x i) (fun j => y j))

def euclidLeft {n m : ℕ} (x : Euclid (n + m)) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun i => x (i.castAdd m))

def euclidRight {n m : ℕ} (x : Euclid (n + m)) : Euclid m :=
  (WithLp.equiv 2 _).symm (fun i => x (i.natAdd n))

@[simp]
theorem euclidAppend_left {n m : ℕ} (x : Euclid n) (y : Euclid m) (i : Fin n) :
    euclidAppend x y (i.castAdd m) = x i := by simp [euclidAppend]

@[simp]
theorem euclidAppend_right {n m : ℕ} (x : Euclid n) (y : Euclid m) (j : Fin m) :
    euclidAppend x y (j.natAdd n) = y j := by simp [euclidAppend]

theorem euclidAppend_blocks {n m : ℕ} (x : Euclid (n + m)) :
    euclidAppend (euclidLeft x) (euclidRight x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [euclidLeft, euclidRight]

theorem euclidAppend_sub {n m : ℕ} (x x' : Euclid n) (y y' : Euclid m) :
    euclidAppend x y - euclidAppend x' y' = euclidAppend (x - x') (y - y') := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem euclidAppend_norm_sq {n m : ℕ} (x : Euclid n) (y : Euclid m) :
    ‖euclidAppend x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [euclid_norm_sq, Fin.sum_univ_add, euclid_norm_sq, euclid_norm_sq]
  simp

theorem euclid_inner_blocks {n m : ℕ} (x y : Euclid (n + m)) :
    ⟪x, y⟫_ℝ = ⟪euclidLeft x, euclidLeft y⟫_ℝ + ⟪euclidRight x, euclidRight y⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply, star_trivial]
  rw [Fin.sum_univ_add]
  rfl

theorem coordinateMultiplier_norm_bound {n : ℕ} (w : Fin n → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, |w i| ≤ C) (x : Euclid n) :
    ‖coordinateMultiplier w x‖ ≤ C * ‖x‖ := by
  have hsq : ‖coordinateMultiplier w x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
    rw [euclid_norm_sq, euclid_norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (hw i) (abs_nonneg (x i))
    have hh := pow_le_pow_left₀ (mul_nonneg (abs_nonneg (w i)) (abs_nonneg (x i))) h 2
    simpa only [coordinateMultiplier_apply, mul_pow, sq_abs] using hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  nlinarith only [hsq]

end FreshGradientMinimax
