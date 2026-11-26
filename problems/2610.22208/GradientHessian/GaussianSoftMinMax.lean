import GradientHessian.GaussianSoftRows

/-! The literal soft minimum of rowwise soft maxima. Its Hessian between
different rows is nonnegative, with no smoothness or derivative premise. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped BigOperators NNReal

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

def softMinMax (α β : ℝ) (x : I × J → ℝ) : ℝ := softMaximum (-α) (softRows β x)

theorem softMinMax_contDiff (α β : ℝ) : ContDiff ℝ ⊤ (softMinMax (I := I) (J := J) α β) :=
  (softMaximum_contDiff (-α)).comp (softRows_contDiff β)

theorem softMinMax_lipschitz {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    LipschitzWith 1 (softMinMax (I := I) (J := J) α β) := by
  simpa only [one_mul] using (softMaximum_lipschitz (neg_ne_zero.mpr hα)).comp (softRows_lipschitz hβ)

theorem softMinMax_hessian_apply {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (x u v : I × J → ℝ) :
    fderiv ℝ (fderiv ℝ (softMinMax α β)) x u v =
      softMaximumHessian (-α) (softRows β x) (softRowsDerivative β x u) (softRowsDerivative β x v) +
      softMaximumDerivative (-α) (softRows β x) (fderiv ℝ (fderiv ℝ (softRows β)) x u v) := by
  have h := second_fderiv_comp_apply ((softMaximum_contDiff (-α)).of_le le_top)
    ((softRows_contDiff β).of_le le_top) x u v
  simpa only [softMaximum_hessian (neg_ne_zero.mpr hα), softRows_fderiv hβ,
    softMaximum_fderiv (neg_ne_zero.mpr hα)] using h

theorem softMinMax_hessian_bound {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (x : I × J → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (softMinMax α β)) x‖ ≤ 2 * |α| + 2 * |β| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hd (w : I × J → ℝ) : ‖softRowsDerivative β x w‖ ≤ ‖w‖ :=
    ((softRowsDerivative β x).le_opNorm w).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (softRowsDerivative_bound β x) (norm_nonneg w))
  have hout : ‖softMaximumHessian (-α) (softRows β x)
      (softRowsDerivative β x u) (softRowsDerivative β x v)‖ ≤ 2 * |α| * ‖u‖ * ‖v‖ := by
    apply ((softMaximumHessian (-α) (softRows β x) _).le_opNorm _).trans
    apply mul_le_mul _ (hd v) (norm_nonneg _) (by positivity)
    apply ((softMaximumHessian (-α) (softRows β x)).le_opNorm _).trans
    exact mul_le_mul (by simpa only [abs_neg] using softMaximumHessian_bound (-α) (softRows β x))
      (hd u) (norm_nonneg _) (by positivity)
  have hin : ‖softMaximumDerivative (-α) (softRows β x)
      (fderiv ℝ (fderiv ℝ (softRows β)) x u v)‖ ≤ 2 * |β| * ‖u‖ * ‖v‖ := by
    apply ((softMaximumDerivative (-α) (softRows β x)).le_opNorm _).trans
    calc
      _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ (softRows β)) x u v‖ :=
        mul_le_mul_of_nonneg_right (softMaximumDerivative_bound (-α) (softRows β x)) (norm_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        apply ((fderiv ℝ (fderiv ℝ (softRows β)) x u).le_opNorm v).trans
        exact mul_le_mul_of_nonneg_right
          (((fderiv ℝ (fderiv ℝ (softRows β)) x).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right (softRows_hessian_bound hβ x) (norm_nonneg u))) (norm_nonneg v)
  rw [softMinMax_hessian_apply hα hβ]
  exact (norm_add_le _ _).trans ((add_le_add hout hin).trans_eq (by ring))

variable [DecidableEq I] [DecidableEq J]

theorem softMinMax_hessian_differentRows {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (x : I × J → ℝ) (i k : I) (j l : J) (hik : i ≠ k) :
    fderiv ℝ (fderiv ℝ (softMinMax α β)) x (Pi.single (i,j) 1) (Pi.single (k,l) 1) =
      α * softWeight (-α) (softRows β x) i * softWeight (-α) (softRows β x) k *
        softWeight β (rowProjection i x) j * softWeight β (rowProjection k x) l := by
  rw [softMinMax_hessian_apply hα hβ, softRows_hessian_different_rows hβ x i k j l hik,
    map_zero, add_zero, softRowsDerivative_single, softRowsDerivative_single]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [softMaximumHessian_apply]
  simp [softMaximumDerivative_apply, Pi.single_apply, hik, Ne.symm hik]
  ring

theorem softMinMax_hessian_differentRows_nonneg {α β : ℝ} (hα : 0 < α) (hβ : β ≠ 0)
    (x : I × J → ℝ) (i k : I) (j l : J) (hik : i ≠ k) :
    0 ≤ fderiv ℝ (fderiv ℝ (softMinMax α β)) x (Pi.single (i,j) 1) (Pi.single (k,l) 1) := by
  rw [softMinMax_hessian_differentRows hα.ne' hβ x i k j l hik]
  exact le_of_lt (mul_pos (mul_pos (mul_pos (mul_pos hα (softWeight_pos _ _ _))
    (softWeight_pos _ _ _)) (softWeight_pos _ _ _)) (softWeight_pos _ _ _))

end GradientHessian.GaussianConcentration
