import GradientHessian.FirstHeightInduction

/-! One higher hierarchy layer is a Euclidean sum of the shared lower space
and eight parent vectors. There is no node-indexed physical coordinate. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open EuclideanRegisters

abbrev Layer (F E : Type*) := WithLp 2 (F × PiLp 2 (fun _ : Fin 8 => E))

variable (F E : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lower : Layer F E →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ F (Registers E 8)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ F (Registers E 8)).toContinuousLinearMap
def parent : Layer F E →L[ℝ] Registers E 8 :=
  (ContinuousLinearMap.snd ℝ F (Registers E 8)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ F (Registers E 8)).toContinuousLinearMap
def parentAt (i : Fin 8) : Layer F E →L[ℝ] E := (PiLp.proj 2 _ i).comp (parent F E)

def insertLower : F →L[ℝ] Layer F E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F (Registers E 8)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ F (Registers E 8))
def insertParentFamily : Registers E 8 →L[ℝ] Layer F E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F (Registers E 8)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ F (Registers E 8))
def insertParent (i : Fin 8) : E →L[ℝ] Layer F E :=
  (insertParentFamily F E).comp (InnerCoordinates.single E 8 i)

theorem lower_apply (Z : Layer F E) : lower F E Z = Z.fst := rfl
theorem parent_apply (Z : Layer F E) : parent F E Z = Z.snd := rfl
@[simp] theorem parentAt_apply (i : Fin 8) (Z : Layer F E) : parentAt F E i Z = parent F E Z i := rfl
@[simp] theorem lower_insertLower (x : F) : lower F E (insertLower F E x) = x := rfl
@[simp] theorem parent_insertLower (x : F) : parent F E (insertLower F E x) = 0 := rfl
@[simp] theorem lower_insertParentFamily (U : Registers E 8) : lower F E (insertParentFamily F E U) = 0 := rfl
@[simp] theorem parent_insertParentFamily (U : Registers E 8) : parent F E (insertParentFamily F E U) = U := rfl

theorem lower_norm_le : ‖lower F E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Z
  simpa only [one_mul] using WithLp.norm_fst_le F Z
theorem parent_norm_le : ‖parent F E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Z
  simpa only [one_mul] using WithLp.norm_snd_le F Z
theorem parentAt_norm_le (i : Fin 8) : ‖parentAt F E i‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (LatchDerivativeSums.projection_norm_le i) (parent_norm_le F E)
      (norm_nonneg (parent F E)) zero_le_one).trans_eq (one_mul 1))
theorem insertLower_norm (x : F) : ‖insertLower F E x‖ = ‖x‖ :=
  WithLp.norm_equiv_symm_fst 2 F (Registers E 8) x
theorem insertParentFamily_norm (U : Registers E 8) : ‖insertParentFamily F E U‖ = ‖U‖ :=
  WithLp.norm_equiv_symm_snd 2 F (Registers E 8) U
theorem insertParent_norm (i : Fin 8) (x : E) : ‖insertParent F E i x‖ = ‖x‖ := by
  simp only [insertParent, ContinuousLinearMap.comp_apply, insertParentFamily_norm, InnerCoordinates.single_norm]
theorem insertLower_norm_le : ‖insertLower F E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [insertLower_norm, one_mul, le_refl]
theorem insertParent_norm_le (i : Fin 8) : ‖insertParent F E i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [insertParent_norm, one_mul, le_refl]

variable {F E}

def replaceLower (Z : Layer F E) (x : F) : Layer F E := Z + insertLower F E (x - lower F E Z)
def replaceParent (Z : Layer F E) (i : Fin 8) (x : E) : Layer F E :=
  Z + insertParent F E i (x - parent F E Z i)

@[simp] theorem replaceLower_self (Z : Layer F E) : replaceLower Z (lower F E Z) = Z := by simp [replaceLower]
@[simp] theorem replaceParent_self (Z : Layer F E) (i : Fin 8) : replaceParent Z i (parent F E Z i) = Z := by
  simp [replaceParent]
@[simp] theorem lower_replaceLower (Z : Layer F E) (x : F) : lower F E (replaceLower Z x) = x := by
  simp [replaceLower]
@[simp] theorem parent_replaceLower (Z : Layer F E) (x : F) : parent F E (replaceLower Z x) = parent F E Z := by
  simp [replaceLower]
@[simp] theorem lower_replaceParent (Z : Layer F E) (i : Fin 8) (x : E) :
    lower F E (replaceParent Z i x) = lower F E Z := by simp [replaceParent, insertParent]
@[simp] theorem parent_replaceParent (Z : Layer F E) (i j : Fin 8) (x : E) :
    parent F E (replaceParent Z i x) j = if j = i then x else parent F E Z j := by
  by_cases h : j = i
  · subst j; simp [replaceParent, insertParent, InnerCoordinates.single_apply, PiLp.add_apply]
  · simp [replaceParent, insertParent, InnerCoordinates.single_apply, PiLp.add_apply, h]

theorem replaceLower_contDiff (Z : Layer F E) : ContDiff ℝ 3 (replaceLower Z) :=
  contDiff_const.add ((insertLower F E).contDiff.comp (contDiff_id.sub contDiff_const))
theorem replaceParent_contDiff (Z : Layer F E) (i : Fin 8) : ContDiff ℝ 3 (replaceParent Z i) :=
  contDiff_const.add ((insertParent F E i).contDiff.comp (contDiff_id.sub contDiff_const))

variable [CompleteSpace F] [CompleteSpace E]

theorem lower_gradient_norm_le (f : Layer F E → ℝ) (Z : Layer F E) (hf : DifferentiableAt ℝ f Z) :
    ‖gradient (fun x => f (replaceLower Z x)) (lower F E Z)‖ ≤ ‖gradient f Z‖ :=
  InnerCoordinates.affine_centered_gradient_norm_le _ (insertLower_norm_le F E) Z _ f hf
theorem parent_gradient_norm_le (f : Layer F E → ℝ) (Z : Layer F E) (i : Fin 8)
    (hf : DifferentiableAt ℝ f Z) :
    ‖gradient (fun x => f (replaceParent Z i x)) (parent F E Z i)‖ ≤ ‖gradient f Z‖ :=
  InnerCoordinates.affine_centered_gradient_norm_le _ (insertParent_norm_le F E i) Z _ f hf

end GradientHessian.HigherHierarchy
