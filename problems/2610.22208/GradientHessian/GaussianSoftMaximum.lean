import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.BigOperators.Field

/-! The finite soft maximum used in Gaussian comparison: actual smooth
function, normalized positive weights, and its actual first derivative. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped BigOperators NNReal

variable {I : Type*} [Fintype I] [Nonempty I]

def softPartition (β : ℝ) (x : I → ℝ) : ℝ := ∑ i, Real.exp (β * x i)
def softWeight (β : ℝ) (x : I → ℝ) (i : I) : ℝ := Real.exp (β * x i) / softPartition β x
def softMaximum (β : ℝ) (x : I → ℝ) : ℝ := Real.log (softPartition β x) / β
def softMaximumDerivative (β : ℝ) (x : I → ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  ∑ i, softWeight β x i • ContinuousLinearMap.proj i

theorem softPartition_pos (β : ℝ) (x : I → ℝ) : 0 < softPartition β x := by
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem softWeight_pos (β : ℝ) (x : I → ℝ) (i : I) : 0 < softWeight β x i :=
  div_pos (Real.exp_pos _) (softPartition_pos β x)

theorem softWeight_sum (β : ℝ) (x : I → ℝ) : (∑ i, softWeight β x i) = 1 := by
  simp only [softWeight, ← Finset.sum_div]
  exact div_self (softPartition_pos β x).ne'

theorem softWeight_le_one (β : ℝ) (x : I → ℝ) (i : I) : softWeight β x i ≤ 1 := by
  rw [← softWeight_sum β x]
  exact Finset.single_le_sum (fun j _ => (softWeight_pos β x j).le) (Finset.mem_univ i)

omit [Nonempty I] in
theorem softPartition_contDiff (β : ℝ) : ContDiff ℝ ⊤ (softPartition (I := I) β) := by
  unfold softPartition
  apply ContDiff.sum
  intro i _
  exact (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp

theorem softWeight_contDiff (β : ℝ) (i : I) : ContDiff ℝ ⊤ (fun x : I → ℝ => softWeight β x i) := by
  exact ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp).div (softPartition_contDiff β)
    (fun x => (softPartition_pos β x).ne')

theorem softMaximum_contDiff (β : ℝ) : ContDiff ℝ ⊤ (softMaximum (I := I) β) := by
  exact ((softPartition_contDiff β).log (fun x => (softPartition_pos β x).ne')).div_const β

omit [Nonempty I] in
theorem softPartition_hasFDerivAt (β : ℝ) (x : I → ℝ) :
    HasFDerivAt (softPartition β)
      (∑ i, (Real.exp (β * x i) * β) • (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ)) x := by
  apply HasFDerivAt.sum
  intro i _
  convert ((ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_mul β).exp using 1
  simp only [smul_smul, ContinuousLinearMap.proj_apply]

theorem softMaximum_hasFDerivAt {β : ℝ} (hβ : β ≠ 0) (x : I → ℝ) :
    HasFDerivAt (softMaximum β) (softMaximumDerivative β x) x := by
  have h := ((softPartition_hasFDerivAt β x).log (softPartition_pos β x).ne').mul_const β⁻¹
  convert h using 1
  ext u
  simp only [softMaximumDerivative, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [softWeight]
  field_simp [hβ, (softPartition_pos β x).ne']
  ring

theorem softMaximum_fderiv {β : ℝ} (hβ : β ≠ 0) (x : I → ℝ) :
    fderiv ℝ (softMaximum β) x = softMaximumDerivative β x :=
  (softMaximum_hasFDerivAt hβ x).fderiv

omit [Nonempty I] in
theorem softMaximumDerivative_apply (β : ℝ) (x u : I → ℝ) :
    softMaximumDerivative β x u = ∑ i, softWeight β x i * u i := by
  simp [softMaximumDerivative]

theorem softMaximumDerivative_bound (β : ℝ) (x : I → ℝ) :
    ‖softMaximumDerivative β x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [softMaximumDerivative_apply]
  calc
    ‖∑ i, softWeight β x i * u i‖ ≤ ∑ i, ‖softWeight β x i * u i‖ := norm_sum_le _ _
    _ ≤ ∑ i, softWeight β x i * ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (softWeight_pos β x i)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (softWeight_pos β x i).le
    _ = 1 * ‖u‖ := by rw [← Finset.sum_mul, softWeight_sum]

theorem softMaximum_lipschitz {β : ℝ} (hβ : β ≠ 0) :
    LipschitzWith 1 (softMaximum (I := I) β) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((softMaximum_contDiff β).differentiable (by norm_num))
  intro x
  rw [softMaximum_fderiv hβ]
  exact_mod_cast softMaximumDerivative_bound β x

end GradientHessian.GaussianConcentration
