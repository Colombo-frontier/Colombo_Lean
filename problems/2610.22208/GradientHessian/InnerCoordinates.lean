import GradientHessian.EuclideanRegisters
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The inner construction uses the Hilbert direct sum of the numerical
coordinate and all physical registers. Every coordinate restriction below is
an actual isometric affine slice of this Euclidean norm. -/

noncomputable section
namespace GradientHessian.InnerCoordinates

open EuclideanRegisters
open scoped InnerProductSpace

variable (Y E : Type*) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Space (m k : ℕ) := WithLp 2 (Y × Registers (Registers E k) m)

def single (n : ℕ) (i : Fin n) : E →L[ℝ] Registers E n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => if j = i then ContinuousLinearMap.id ℝ E else 0))

@[simp] theorem single_apply (n : ℕ) (i j : Fin n) (x : E) :
    single E n i x j = if j = i then x else 0 := by
  by_cases h : j = i <;> simp [single, h]

theorem single_norm (n : ℕ) (i : Fin n) (x : E) : ‖single E n i x‖ = ‖x‖ := by
  have h : ‖single E n i x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [single_apply, apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)]
    simp
  nlinarith [norm_nonneg (single E n i x), norm_nonneg x]

theorem single_norm_le (n : ℕ) (i : Fin n) : ‖single E n i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [single_norm]

def numerical (m k : ℕ) : Space Y E m k →L[ℝ] Y :=
  (ContinuousLinearMap.fst ℝ Y (Registers (Registers E k) m)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ Y (Registers (Registers E k) m)).toContinuousLinearMap

def tasks (m k : ℕ) : Space Y E m k →L[ℝ] Registers (Registers E k) m :=
  (ContinuousLinearMap.snd ℝ Y (Registers (Registers E k) m)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ Y (Registers (Registers E k) m)).toContinuousLinearMap

def insertNumerical (m k : ℕ) : Y →L[ℝ] Space Y E m k :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Y (Registers (Registers E k) m)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ Y (Registers (Registers E k) m))

def insertTasks (m k : ℕ) : Registers (Registers E k) m →L[ℝ] Space Y E m k :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Y (Registers (Registers E k) m)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ Y (Registers (Registers E k) m))

def insertTask (m k : ℕ) (i : Fin m) : Registers E k →L[ℝ] Space Y E m k :=
  (insertTasks Y E m k).comp (single (Registers E k) m i)

def insertRegister (m k : ℕ) (i : Fin m) (j : Fin k) : E →L[ℝ] Space Y E m k :=
  (insertTask Y E m k i).comp (single E k j)

@[simp] theorem numerical_insertNumerical (m k : ℕ) (y : Y) :
    numerical Y E m k (insertNumerical Y E m k y) = y := rfl
@[simp] theorem tasks_insertNumerical (m k : ℕ) (y : Y) :
    tasks Y E m k (insertNumerical Y E m k y) = 0 := rfl
@[simp] theorem numerical_insertTasks (m k : ℕ) (U : Registers (Registers E k) m) :
    numerical Y E m k (insertTasks Y E m k U) = 0 := rfl
@[simp] theorem tasks_insertTasks (m k : ℕ) (U : Registers (Registers E k) m) :
    tasks Y E m k (insertTasks Y E m k U) = U := rfl

theorem insertNumerical_norm (m k : ℕ) (y : Y) :
    ‖insertNumerical Y E m k y‖ = ‖y‖ :=
  WithLp.norm_equiv_symm_fst 2 Y (Registers (Registers E k) m) y
theorem insertTasks_norm (m k : ℕ) (U : Registers (Registers E k) m) :
    ‖insertTasks Y E m k U‖ = ‖U‖ :=
  WithLp.norm_equiv_symm_snd 2 Y (Registers (Registers E k) m) U
theorem insertTask_norm (m k : ℕ) (i : Fin m) (U : Registers E k) :
    ‖insertTask Y E m k i U‖ = ‖U‖ := by
  simp only [insertTask, ContinuousLinearMap.comp_apply, insertTasks_norm, single_norm]
theorem insertRegister_norm (m k : ℕ) (i : Fin m) (j : Fin k) (x : E) :
    ‖insertRegister Y E m k i j x‖ = ‖x‖ := by
  simp only [insertRegister, ContinuousLinearMap.comp_apply, insertTask_norm, single_norm]

theorem insertNumerical_norm_le (m k : ℕ) : ‖insertNumerical Y E m k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [insertNumerical_norm]
theorem insertTask_norm_le (m k : ℕ) (i : Fin m) : ‖insertTask Y E m k i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [insertTask_norm]
theorem insertRegister_norm_le (m k : ℕ) (i : Fin m) (j : Fin k) :
    ‖insertRegister Y E m k i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [insertRegister_norm]

variable {Y E}

def replaceNumerical {m k : ℕ} (Z : Space Y E m k) (y : Y) : Space Y E m k :=
  Z + insertNumerical Y E m k (y - numerical Y E m k Z)
def replaceTask {m k : ℕ} (Z : Space Y E m k) (i : Fin m) (U : Registers E k) :
    Space Y E m k := Z + insertTask Y E m k i (U - tasks Y E m k Z i)
def replaceRegister {m k : ℕ} (Z : Space Y E m k) (i : Fin m) (j : Fin k) (x : E) :
    Space Y E m k := Z + insertRegister Y E m k i j (x - tasks Y E m k Z i j)

@[simp] theorem replaceNumerical_self {m k : ℕ} (Z : Space Y E m k) :
    replaceNumerical Z (numerical Y E m k Z) = Z := by simp [replaceNumerical]
@[simp] theorem replaceTask_self {m k : ℕ} (Z : Space Y E m k) (i : Fin m) :
    replaceTask Z i (tasks Y E m k Z i) = Z := by simp [replaceTask]
@[simp] theorem replaceRegister_self {m k : ℕ} (Z : Space Y E m k) (i : Fin m) (j : Fin k) :
    replaceRegister Z i j (tasks Y E m k Z i j) = Z := by simp [replaceRegister]

@[simp] theorem numerical_replaceNumerical {m k : ℕ} (Z : Space Y E m k) (y : Y) :
    numerical Y E m k (replaceNumerical Z y) = y := by simp [replaceNumerical]
@[simp] theorem tasks_replaceNumerical {m k : ℕ} (Z : Space Y E m k) (y : Y) :
    tasks Y E m k (replaceNumerical Z y) = tasks Y E m k Z := by simp [replaceNumerical]

@[simp] theorem numerical_replaceTask {m k : ℕ} (Z : Space Y E m k) (i : Fin m)
    (U : Registers E k) : numerical Y E m k (replaceTask Z i U) = numerical Y E m k Z := by
  simp [replaceTask, insertTask]
@[simp] theorem tasks_replaceTask {m k : ℕ} (Z : Space Y E m k) (i j : Fin m)
    (U : Registers E k) : tasks Y E m k (replaceTask Z i U) j =
      if j = i then U else tasks Y E m k Z j := by
  by_cases h : j = i
  · subst j
    simp [replaceTask, insertTask, single_apply, PiLp.add_apply]
  · simp [replaceTask, insertTask, single_apply, PiLp.add_apply, h]

variable [CompleteSpace Y] [CompleteSpace E]

theorem affine_centered_gradient_norm_le {F G : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G] (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (Z : G) (x : F) (f : G → ℝ) (hf : DifferentiableAt ℝ f Z) :
    ‖gradient (fun y => f (Z + L (y - x))) x‖ ≤ ‖gradient f Z‖ := by
  have he : Z - L x + L x = Z := sub_add_cancel _ _
  have h := affine_gradient_norm_le L hL (Z - L x) f x (by rwa [he])
  rw [he] at h
  have hfun : (fun y => f (Z + L (y - x))) = (fun y => f (Z - L x + L y)) := by
    funext y
    congr 1
    rw [map_sub]
    abel
  rwa [hfun]

theorem numerical_slice_gradient_norm_le {m k : ℕ} (Z : Space Y E m k)
    (f : Space Y E m k → ℝ) (hf : DifferentiableAt ℝ f Z) :
    ‖gradient (fun y => f (replaceNumerical Z y)) (numerical Y E m k Z)‖ ≤ ‖gradient f Z‖ :=
  affine_centered_gradient_norm_le _ (insertNumerical_norm_le Y E m k) Z _ f hf
theorem task_slice_gradient_norm_le {m k : ℕ} (Z : Space Y E m k) (i : Fin m)
    (f : Space Y E m k → ℝ) (hf : DifferentiableAt ℝ f Z) :
    ‖gradient (fun U => f (replaceTask Z i U)) (tasks Y E m k Z i)‖ ≤ ‖gradient f Z‖ :=
  affine_centered_gradient_norm_le _ (insertTask_norm_le Y E m k i) Z _ f hf
theorem register_slice_gradient_norm_le {m k : ℕ} (Z : Space Y E m k)
    (i : Fin m) (j : Fin k) (f : Space Y E m k → ℝ) (hf : DifferentiableAt ℝ f Z) :
    ‖gradient (fun x => f (replaceRegister Z i j x)) (tasks Y E m k Z i j)‖ ≤ ‖gradient f Z‖ :=
  affine_centered_gradient_norm_le _ (insertRegister_norm_le Y E m k i j) Z _ f hf

end GradientHessian.InnerCoordinates
