import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

/-! Euclidean, rather than supremum, norms for finite families of registers. -/

noncomputable section
namespace GradientHessian.EuclideanRegisters

open scoped InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Registers (n : ℕ) := PiLp 2 (fun _ : Fin n => E)

instance registersCompleteSpace [CompleteSpace E] (n : ℕ) : CompleteSpace (Registers E n) :=
  Pi.complete (fun _ : Fin n => E)

def head (n : ℕ) : Registers E (n + 1) →L[ℝ] E := PiLp.proj 2 _ 0

def tail (n : ℕ) : Registers E (n + 1) →L[ℝ] Registers E n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin n => PiLp.proj 2 _ i.succ))

def insertHead (n : ℕ) : E →L[ℝ] Registers E (n + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin (n + 1) => Fin.cases (ContinuousLinearMap.id ℝ E)
      (fun _ => (0 : E →L[ℝ] E)) i))

def insertTail (n : ℕ) : Registers E n →L[ℝ] Registers E (n + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin (n + 1) => Fin.cases (0 : Registers E n →L[ℝ] E)
      (fun j => PiLp.proj 2 _ j) i))

@[simp] theorem head_apply (n : ℕ) (U : Registers E (n + 1)) : head E n U = U 0 := rfl
@[simp] theorem tail_apply (n : ℕ) (U : Registers E (n + 1)) (i : Fin n) :
    tail E n U i = U i.succ := rfl

@[simp] theorem insertHead_zero (n : ℕ) (x : E) : insertHead E n x 0 = x := rfl
@[simp] theorem insertHead_succ (n : ℕ) (x : E) (i : Fin n) : insertHead E n x i.succ = 0 := rfl
@[simp] theorem insertTail_zero (n : ℕ) (U : Registers E n) : insertTail E n U 0 = 0 := rfl
@[simp] theorem insertTail_succ (n : ℕ) (U : Registers E n) (i : Fin n) :
    insertTail E n U i.succ = U i := rfl

theorem insertHead_norm (n : ℕ) (x : E) : ‖insertHead E n x‖ = ‖x‖ := by
  have h : ‖insertHead E n x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
    simp
  nlinarith [norm_nonneg (insertHead E n x), norm_nonneg x]

theorem insertTail_norm (n : ℕ) (U : Registers E n) : ‖insertTail E n U‖ = ‖U‖ := by
  have h : ‖insertTail E n U‖ ^ 2 = ‖U‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, PiLp.norm_sq_eq_of_L2]
    simp
  nlinarith [norm_nonneg (insertTail E n U), norm_nonneg U]

theorem insertHead_norm_le (n : ℕ) : ‖insertHead E n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [insertHead_norm]

theorem insertTail_norm_le (n : ℕ) : ‖insertTail E n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro U
  simp [insertTail_norm]

def join {n : ℕ} (x : E) (U : Registers E n) : Registers E (n + 1) :=
  insertHead E n x + insertTail E n U

@[simp] theorem join_zero {n : ℕ} (x : E) (U : Registers E n) : join E x U 0 = x := by
  simp [join, PiLp.add_apply]

@[simp] theorem join_succ {n : ℕ} (x : E) (U : Registers E n) (i : Fin n) :
    join E x U i.succ = U i := by simp [join, PiLp.add_apply]

@[simp] theorem tail_join {n : ℕ} (x : E) (U : Registers E n) : tail E n (join E x U) = U := by
  ext i
  simp

@[simp] theorem join_head_tail {n : ℕ} (U : Registers E (n + 1)) :
    join E (U 0) (tail E n U) = U := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

variable {E}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]

/-- Restricting to an affine isometric register slice cannot increase the
gradient norm. This uses the actual Hilbert gradient on both spaces. -/
theorem affine_gradient_norm_le (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (a : F) (f : F → ℝ) (x : E) (hf : DifferentiableAt ℝ f (a + L x)) :
    ‖gradient (fun y => f (a + L y)) x‖ ≤ ‖gradient f (a + L x)‖ := by
  have hg := hf.hasFDerivAt.comp x ((hasFDerivAt_const a x).add L.hasFDerivAt)
  have he : fderiv ℝ (fun y => f (a + L y)) x = (fderiv ℝ f (a + L x)).comp L := by
    simpa using hg.fderiv
  simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hL)

theorem head_slice_gradient_norm_le (n : ℕ) (f : Registers E (n + 1) → ℝ)
    (U : Registers E (n + 1)) (hf : DifferentiableAt ℝ f U) :
    ‖gradient (fun x => f (join E x (tail E n U))) (U 0)‖ ≤ ‖gradient f U‖ := by
  have he : insertTail E n (tail E n U) + insertHead E n (U 0) = U := by
    rw [add_comm (insertTail E n (tail E n U)) (insertHead E n (U 0))]
    exact join_head_tail E U
  have h := affine_gradient_norm_le (insertHead E n) (insertHead_norm_le E n)
    (insertTail E n (tail E n U)) f (U 0) (by rwa [he])
  rw [he] at h
  have heq : (fun x => f (join E x (tail E n U))) =
      (fun x => f (insertTail E n (tail E n U) + insertHead E n x)) := by
    funext x
    congr 1
    exact add_comm _ _
  rw [heq]
  exact h

theorem tail_slice_gradient_norm_le (n : ℕ) (f : Registers E (n + 1) → ℝ)
    (U : Registers E (n + 1)) (hf : DifferentiableAt ℝ f U) :
    ‖gradient (fun V => f (join E (U 0) V)) (tail E n U)‖ ≤ ‖gradient f U‖ := by
  have he : insertHead E n (U 0) + insertTail E n (tail E n U) = U := join_head_tail E U
  have h := affine_gradient_norm_le (insertTail E n) (insertTail_norm_le E n)
    (insertHead E n (U 0)) f (tail E n U) (by rwa [he])
  rw [he] at h
  exact h

end GradientHessian.EuclideanRegisters
