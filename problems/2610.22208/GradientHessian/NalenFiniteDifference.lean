import GradientHessian.NalenObjective
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! An actual Hessian approximation from one base gradient and the
coordinate finite differences. The error is measured in operator norm,
with no bound on the Hessian itself. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [Fintype I] [DecidableEq I]

def columnOperator (b : OrthonormalBasis I ℝ E) (c : I → E) : E →L[ℝ] E :=
  ∑ i,(innerSL ℝ (b i)).smulRight (c i)

omit [DecidableEq I] in
theorem columnOperator_apply (b : OrthonormalBasis I ℝ E) (c : I → E) (x : E) :
    columnOperator b c x=∑ i,⟪b i,x⟫_ℝ • c i := by
  simp [columnOperator,ContinuousLinearMap.sum_apply]

@[simp] theorem columnOperator_basis (b : OrthonormalBasis I ℝ E) (c : I → E) (i : I) :
    columnOperator b c (b i)=c i := by
  rw [columnOperator_apply]
  simp [orthonormal_iff_ite.mp b.orthonormal]

omit [DecidableEq I] in
theorem columnOperator_continuous (b : OrthonormalBasis I ℝ E) : Continuous (columnOperator b) := by
  unfold columnOperator
  apply continuous_finset_sum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ E E) (innerSL ℝ (b i))).continuous.comp (continuous_apply i)

omit [DecidableEq I] in
theorem sum_norm_coordinates_le (b : OrthonormalBasis I ℝ E) (x : E) :
    (∑ i,‖⟪b i,x⟫_ℝ‖) ≤ Real.sqrt (Fintype.card I)*‖x‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖⟪b i,x⟫_ℝ‖) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  rw [b.sum_sq_norm_inner] at h
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  nlinarith only [h]

omit [DecidableEq I] in
theorem operator_norm_of_columns (b : OrthonormalBasis I ℝ E) (A : E →L[ℝ] E)
    {c : ℝ} (hc : 0 ≤ c) (hA : ∀ i,‖A (b i)‖ ≤ c) :
    ‖A‖ ≤ Real.sqrt (Fintype.card I)*c := by
  apply A.opNorm_le_bound (mul_nonneg (Real.sqrt_nonneg _) hc)
  intro x
  have he : A x=∑ i,⟪b i,x⟫_ℝ • A (b i) := by
    calc
      A x=A (∑ i,⟪b i,x⟫_ℝ • b i) := by rw [b.sum_repr']
      _ = _ := by simp only [map_sum,map_smul]
  rw [he]
  calc
    ‖∑ i,⟪b i,x⟫_ℝ • A (b i)‖ ≤ ∑ i,‖⟪b i,x⟫_ℝ • A (b i)‖ := norm_sum_le _ _
    _ = ∑ i,‖⟪b i,x⟫_ℝ‖*‖A (b i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i,‖⟪b i,x⟫_ℝ‖*c := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hA i) (norm_nonneg _))
    _ = (∑ i,‖⟪b i,x⟫_ℝ‖)*c := (Finset.sum_mul _ _ _).symm
    _ ≤ (Real.sqrt (Fintype.card I)*‖x‖)*c :=
      mul_le_mul_of_nonneg_right (sum_norm_coordinates_le b x) hc
    _ = _ := by ring

variable [CompleteSpace E]

def finiteDifference (b : OrthonormalBasis I ℝ E) (f : E → ℝ) (z : E) (a : ℝ) : E →L[ℝ] E :=
  columnOperator b (fun i => a⁻¹ • (gradient f (z+a • b i)-gradient f z))

theorem finiteDifference_column_error (b : OrthonormalBasis I ℝ E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f)))
    (z : E) {a : ℝ} (ha : 0 < a) (i : I) :
    ‖(finiteDifference b f z a-hessianOperator f z) (b i)‖ ≤ a := by
  have he : (finiteDifference b f z a-hessianOperator f z) (b i)=
      a⁻¹ • (gradient f (z+a • b i)-gradient f z-hessianOperator f z (a • b i)) := by
    simp [finiteDifference,smul_sub,map_smul,smul_smul,ha.ne']
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  have ht := gradient_taylor hf hL z (z+a • b i)
  simp only [add_sub_cancel_left,NNReal.coe_one,one_mul,norm_smul,Real.norm_eq_abs,
    abs_of_pos ha,b.norm_eq_one,mul_one] at ht
  have h := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr ha.le)
  have he' : a⁻¹*a^2=a := by field_simp; ring
  simpa only [he'] using h

theorem finiteDifference_error (b : OrthonormalBasis I ℝ E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f)))
    (z : E) {a : ℝ} (ha : 0 < a) :
    ‖finiteDifference b f z a-hessianOperator f z‖ ≤ Real.sqrt (Fintype.card I)*a :=
  operator_norm_of_columns b _ ha.le (finiteDifference_column_error b hf hL z ha)

end GradientHessian.Nalen
