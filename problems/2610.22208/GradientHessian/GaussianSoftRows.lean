import GradientHessian.GaussianSoftMaximumHessian
import GradientHessian.GaussianSecondChainRule

/-! Actual rowwise soft maxima on a finite array, with their first and
second derivatives and dimension-independent operator bounds. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped BigOperators NNReal

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]

def rowProjection (i : I) : (I × J → ℝ) →L[ℝ] (J → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (i,j))

omit [Fintype I] [Fintype J] [Nonempty J] in
@[simp] theorem rowProjection_apply (i : I) (x : I × J → ℝ) (j : J) :
    rowProjection i x j = x (i,j) := rfl

omit [Nonempty J] in
theorem rowProjection_norm (i : I) (x : I × J → ℝ) : ‖rowProjection i x‖ ≤ ‖x‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun j => norm_le_pi_norm x (i,j))

def softRows (β : ℝ) (x : I × J → ℝ) : I → ℝ := fun i => softMaximum β (rowProjection i x)

theorem softRows_contDiff (β : ℝ) : ContDiff ℝ ⊤ (softRows (I := I) (J := J) β) := by
  apply contDiff_pi.mpr
  intro i
  exact (softMaximum_contDiff β).comp (rowProjection (J := J) i).contDiff

def softRowsDerivative (β : ℝ) (x : I × J → ℝ) : (I × J → ℝ) →L[ℝ] (I → ℝ) :=
  ContinuousLinearMap.pi (fun i => (softMaximumDerivative β (rowProjection i x)).comp (rowProjection i))

theorem softRows_hasFDerivAt {β : ℝ} (hβ : β ≠ 0) (x : I × J → ℝ) :
    HasFDerivAt (softRows β) (softRowsDerivative β x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (softMaximum_hasFDerivAt hβ _).comp x (rowProjection (J := J) i).hasFDerivAt

theorem softRows_fderiv {β : ℝ} (hβ : β ≠ 0) (x : I × J → ℝ) :
    fderiv ℝ (softRows β) x = softRowsDerivative β x := (softRows_hasFDerivAt hβ x).fderiv

omit [Fintype I] [Nonempty J] in
@[simp] theorem softRowsDerivative_apply (β : ℝ) (x u : I × J → ℝ) (i : I) :
    softRowsDerivative β x u i = softMaximumDerivative β (rowProjection i x) (rowProjection i u) := rfl

theorem softRowsDerivative_bound (β : ℝ) (x : I × J → ℝ) : ‖softRowsDerivative β x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro i
  exact ((softMaximumDerivative β (rowProjection i x)).le_opNorm _).trans
    (by simpa only [one_mul] using (mul_le_mul
      (softMaximumDerivative_bound β (rowProjection i x)) (rowProjection_norm i u)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))

theorem softRows_lipschitz {β : ℝ} (hβ : β ≠ 0) :
    LipschitzWith 1 (softRows (I := I) (J := J) β) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((softRows_contDiff β).differentiable (by norm_num))
  intro x
  rw [softRows_fderiv hβ]
  exact_mod_cast softRowsDerivative_bound β x

theorem softRows_hessian_apply {β : ℝ} (hβ : β ≠ 0) (x u v : I × J → ℝ) (i : I) :
    fderiv ℝ (fderiv ℝ (softRows β)) x u v i =
      softMaximumHessian β (rowProjection i x) (rowProjection i u) (rowProjection i v) := by
  have h1 := second_fderiv_linear_postcomp_apply ((softRows_contDiff β).of_le le_top)
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ) x u v
  have h2 := second_fderiv_linear_comp_apply ((softMaximum_contDiff β).of_le le_top)
    (rowProjection i) x u v
  rw [softMaximum_hessian hβ] at h2
  exact h1.symm.trans h2

theorem softRows_hessian_bound {β : ℝ} (hβ : β ≠ 0) (x : I × J → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (softRows β)) x‖ ≤ 2 * |β| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * |β| * ‖u‖) * ‖v‖)).mpr
  intro i
  rw [softRows_hessian_apply hβ]
  calc
    _ ≤ ‖softMaximumHessian β (rowProjection i x) (rowProjection i u)‖ * ‖rowProjection i v‖ :=
      (softMaximumHessian β (rowProjection i x) (rowProjection i u)).le_opNorm _
    _ ≤ (‖softMaximumHessian β (rowProjection i x)‖ * ‖rowProjection i u‖) * ‖rowProjection i v‖ :=
      mul_le_mul_of_nonneg_right ((softMaximumHessian β (rowProjection i x)).le_opNorm _)
        (norm_nonneg _)
    _ ≤ _ := mul_le_mul
      (mul_le_mul (softMaximumHessian_bound β _) (rowProjection_norm i u) (norm_nonneg _) (by positivity))
      (rowProjection_norm i v) (norm_nonneg _) (by positivity)

variable [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] [Nonempty J] in
theorem rowProjection_single_same (i : I) (j : J) :
    rowProjection i (Pi.single (i,j) 1) = Pi.single j 1 := by
  ext k
  simp [Pi.single_apply]

omit [Fintype I] [Fintype J] [Nonempty J] in
theorem rowProjection_single_other (i k : I) (j : J) (h : i ≠ k) :
    rowProjection i (Pi.single (k,j) 1) = 0 := by
  ext l
  simp [Pi.single_apply, Ne.symm h]

omit [Fintype I] [Nonempty J] in
theorem softRowsDerivative_single (β : ℝ) (x : I × J → ℝ) (i : I) (j : J) :
    softRowsDerivative β x (Pi.single (i,j) 1) =
      softWeight β (rowProjection i x) j • (Pi.single i (1 : ℝ) : I → ℝ) := by
  ext k
  by_cases h : k = i
  · subst k
    simp [rowProjection_single_same, softMaximumDerivative_apply, Pi.single_apply]
  · simp [rowProjection_single_other k i j h, Pi.single_apply, Ne.symm h]

theorem softRows_hessian_different_rows {β : ℝ} (hβ : β ≠ 0) (x : I × J → ℝ)
    (i k : I) (j l : J) (hik : i ≠ k) :
    fderiv ℝ (fderiv ℝ (softRows β)) x (Pi.single (i,j) 1) (Pi.single (k,l) 1) = 0 := by
  ext a
  rw [softRows_hessian_apply hβ]
  by_cases h : a = i
  · subst a
    rw [rowProjection_single_other i k l hik, map_zero]
    rfl
  · rw [rowProjection_single_other a i j h, map_zero, ContinuousLinearMap.zero_apply]
    rfl

end GradientHessian.GaussianConcentration
