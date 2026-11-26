import GradientHessian.GaussianSoftMaximum

/-! Actual Hessian of the finite soft maximum, its uniform bound, and
the nonpositive off-diagonal entries used in Gaussian comparison. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped BigOperators NNReal

variable {I : Type*} [Fintype I] [Nonempty I]

theorem softWeight_eq_exp (β : ℝ) (x : I → ℝ) (i : I) :
    softWeight β x i = Real.exp (β * x i - Real.log (softPartition β x)) := by
  rw [Real.exp_sub, Real.exp_log (softPartition_pos β x)]
  rfl

theorem softLogPartition_hasFDerivAt {β : ℝ} (hβ : β ≠ 0) (x : I → ℝ) :
    HasFDerivAt (fun y => Real.log (softPartition β y)) (β • softMaximumDerivative β x) x := by
  have he : (fun y : I → ℝ => β * softMaximum β y) =
      fun y => Real.log (softPartition β y) := by
    funext y
    dsimp [softMaximum]
    field_simp
  rw [← he]
  exact (softMaximum_hasFDerivAt hβ x).const_mul β

def softWeightDerivative (β : ℝ) (x : I → ℝ) (i : I) : (I → ℝ) →L[ℝ] ℝ :=
  (β * softWeight β x i) • (ContinuousLinearMap.proj i - softMaximumDerivative β x)

theorem softWeight_hasFDerivAt {β : ℝ} (hβ : β ≠ 0) (x : I → ℝ) (i : I) :
    HasFDerivAt (fun y => softWeight β y i) (softWeightDerivative β x i) x := by
  simp only [softWeight_eq_exp]
  have h := (((ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_mul β).sub
    (softLogPartition_hasFDerivAt hβ x)).exp
  convert h using 1
  ext u
  simp only [softWeightDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    softWeight_eq_exp]
  ring

def softMaximumHessian (β : ℝ) (x : I → ℝ) : (I → ℝ) →L[ℝ] (I → ℝ) →L[ℝ] ℝ :=
  ∑ i, (softWeightDerivative β x i).smulRight (ContinuousLinearMap.proj i)

theorem softMaximumDerivative_hasFDerivAt {β : ℝ} (hβ : β ≠ 0) (x : I → ℝ) :
    HasFDerivAt (softMaximumDerivative β) (softMaximumHessian β x) x := by
  apply HasFDerivAt.sum
  intro i _
  exact (softWeight_hasFDerivAt hβ x i).smul_const
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ)

theorem softMaximum_hessian {β : ℝ} (hβ : β ≠ 0) (x : I → ℝ) :
    fderiv ℝ (fderiv ℝ (softMaximum β)) x = softMaximumHessian β x := by
  have he : fderiv ℝ (softMaximum (I := I) β) = softMaximumDerivative β :=
    funext (softMaximum_fderiv hβ)
  rw [he]
  exact (softMaximumDerivative_hasFDerivAt hβ x).fderiv

omit [Nonempty I] in
theorem softMaximumHessian_apply (β : ℝ) (x u v : I → ℝ) :
    softMaximumHessian β x u v =
      β * ((∑ i, softWeight β x i * u i * v i) -
        softMaximumDerivative β x u * softMaximumDerivative β x v) := by
  simp only [softMaximumHessian, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, softWeightDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc
    _ = β * ∑ i, (softWeight β x i * u i * v i -
        softMaximumDerivative β x u * (softWeight β x i * v i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← softMaximumDerivative_apply]

theorem softMaximumHessian_bound (β : ℝ) (x : I → ℝ) :
    ‖softMaximumHessian β x‖ ≤ 2 * |β| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hu : ‖softMaximumDerivative β x u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using ((softMaximumDerivative β x).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (softMaximumDerivative_bound β x) (norm_nonneg u))
  have hv : ‖softMaximumDerivative β x v‖ ≤ ‖v‖ := by
    simpa only [one_mul] using ((softMaximumDerivative β x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (softMaximumDerivative_bound β x) (norm_nonneg v))
  have hs : ‖∑ i, softWeight β x i * u i * v i‖ ≤ ‖u‖ * ‖v‖ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i, softWeight β x i * (‖u‖ * ‖v‖) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (softWeight_pos β x i)]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_le_pi_norm u i)
          (norm_le_pi_norm v i) (abs_nonneg _) (norm_nonneg _)) (softWeight_pos β x i).le
      _ = _ := by rw [← Finset.sum_mul, softWeight_sum, one_mul]
  rw [softMaximumHessian_apply, norm_mul, Real.norm_eq_abs]
  have hm : ‖softMaximumDerivative β x u * softMaximumDerivative β x v‖ ≤ ‖u‖ * ‖v‖ := by
    rw [norm_mul]
    exact mul_le_mul hu hv (norm_nonneg _) (norm_nonneg _)
  have hd := (norm_sub_le (∑ i, softWeight β x i * u i * v i)
    (softMaximumDerivative β x u * softMaximumDerivative β x v)).trans (add_le_add hs hm)
  nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg β)]

theorem softMaximum_hessian_bound {β : ℝ} (hβ : β ≠ 0) (x : I → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (softMaximum β)) x‖ ≤ 2 * |β| := by
  rw [softMaximum_hessian hβ]
  exact softMaximumHessian_bound β x

theorem softMaximum_hessian_offDiagonal [DecidableEq I] {β : ℝ} (hβ : 0 < β)
    (x : I → ℝ) (i j : I) (hij : i ≠ j) :
    fderiv ℝ (fderiv ℝ (softMaximum β)) x (Pi.single i 1) (Pi.single j 1) =
      -β * softWeight β x i * softWeight β x j := by
  rw [softMaximum_hessian hβ.ne', softMaximumHessian_apply]
  simp [softMaximumDerivative_apply, Pi.single_apply, hij, Ne.symm hij]
  ring

theorem softMaximum_hessian_offDiagonal_nonpos [DecidableEq I] {β : ℝ} (hβ : 0 < β)
    (x : I → ℝ) (i j : I) (hij : i ≠ j) :
    fderiv ℝ (fderiv ℝ (softMaximum β)) x (Pi.single i 1) (Pi.single j 1) ≤ 0 := by
  rw [softMaximum_hessian_offDiagonal hβ x i j hij]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (softWeight_pos β x i).le)
    (softWeight_pos β x j).le

end GradientHessian.GaussianConcentration
