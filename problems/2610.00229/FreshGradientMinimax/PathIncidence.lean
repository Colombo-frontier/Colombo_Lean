import FreshGradientMinimax.Objective
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Fin

/-! A signed finite path incidence operator, with both endpoint rows.
Zero padding gives its dimension-independent operator norm bound of two. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

theorem euclid_norm_sq {n : ℕ} (x : Euclid n) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x

def pathPadLeft (n : ℕ) : Euclid n →L[ℝ] Euclid (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (WithLp.equiv 2 _).symm (Fin.snoc (α := fun _ => ℝ) (fun i => x i) 0)
      map_add' := by
        intro x y
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp
      map_smul' := by
        intro a x
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp }

def pathPadRight (n : ℕ) : Euclid n →L[ℝ] Euclid (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (WithLp.equiv 2 _).symm (Fin.cons (α := fun _ => ℝ) 0 (fun i => x i))
      map_add' := by
        intro x y
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp
      map_smul' := by
        intro a x
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp }

@[simp]
theorem pathPadLeft_apply {n : ℕ} (x : Euclid n) (i : Fin (n + 1)) :
    pathPadLeft n x i = Fin.snoc (α := fun _ => ℝ) (fun j => x j) 0 i := rfl

@[simp]
theorem pathPadRight_apply {n : ℕ} (x : Euclid n) (i : Fin (n + 1)) :
    pathPadRight n x i = Fin.cons (α := fun _ => ℝ) 0 (fun j => x j) i := rfl

theorem pathPadLeft_norm {n : ℕ} (x : Euclid n) : ‖pathPadLeft n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclid_norm_sq, euclid_norm_sq, Fin.sum_univ_castSucc]
  simp

theorem pathPadRight_norm {n : ℕ} (x : Euclid n) : ‖pathPadRight n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclid_norm_sq, euclid_norm_sq, Fin.sum_univ_succ]
  simp

def coordinateMultiplier {n : ℕ} (s : Fin n → ℝ) : Euclid n →L[ℝ] Euclid n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (WithLp.equiv 2 _).symm (fun i => s i * x i)
      map_add' := by intros; ext i; simp [mul_add]
      map_smul' := by intros; ext i; simp [mul_left_comm] }

@[simp]
theorem coordinateMultiplier_apply {n : ℕ} (s : Fin n → ℝ) (x : Euclid n) (i : Fin n) :
    coordinateMultiplier s x i = s i * x i := rfl

theorem coordinateMultiplier_norm_le {n : ℕ} {s : Fin n → ℝ} (hs : ∀ i, |s i| ≤ 1)
    (x : Euclid n) : ‖coordinateMultiplier s x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclid_norm_sq, euclid_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  have h : |s i * x i| ≤ |x i| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hs i) (abs_nonneg (x i))
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

def pathIncidence {n : ℕ} (s : Fin (n + 1) → ℝ) : Euclid n →L[ℝ] Euclid (n + 1) :=
  pathPadLeft n - (coordinateMultiplier s).comp (pathPadRight n)

@[simp]
theorem pathIncidence_apply {n : ℕ} (s : Fin (n + 1) → ℝ) (x : Euclid n) (i : Fin (n + 1)) :
    pathIncidence s x i = Fin.snoc (α := fun _ => ℝ) (fun j => x j) 0 i - s i * Fin.cons (α := fun _ => ℝ) 0 (fun j => x j) i := rfl

theorem pathIncidence_norm_bound {n : ℕ} {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1)
    (x : Euclid n) : ‖pathIncidence s x‖ ≤ 2 * ‖x‖ := by
  change ‖pathPadLeft n x - coordinateMultiplier s (pathPadRight n x)‖ ≤ _
  have h := norm_sub_le (pathPadLeft n x) (coordinateMultiplier s (pathPadRight n x))
  have hc := coordinateMultiplier_norm_le hs (pathPadRight n x)
  rw [pathPadLeft_norm] at h
  rw [pathPadRight_norm] at hc
  linarith

theorem pathIncidence_opNorm {n : ℕ} {s : Fin (n + 1) → ℝ} (hs : ∀ i, |s i| ≤ 1) :
    ‖pathIncidence s‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (pathIncidence_norm_bound hs)

end FreshGradientMinimax

