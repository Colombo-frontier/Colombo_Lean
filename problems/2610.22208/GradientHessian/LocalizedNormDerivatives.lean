import GradientHessian.SmoothNormCompression
import GradientHessian.Localized
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual dimension-independent higher derivatives of the smoothed norm used
by the localized public baseline and drive. No derivative estimate is assumed. -/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace GradientHessian.LocalizedNormDerivatives
open SmoothNormCompression Localized

section Normed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_first_derivative (f : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := by
  simpa only [iteratedFDerivWithin_univ, fderivWithin_univ] using
    norm_iteratedFDerivWithin_one (𝕜 := ℝ) (s := Set.univ) (x := x) f uniqueDiffWithinAt_univ

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitSmoothNorm (x : E) : ℝ := Real.sqrt (1+‖x‖^2)
def smoothNorm (w : ℝ) (x : E) : ℝ := Real.sqrt (w^2+‖x‖^2)

theorem unitSmoothNorm_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n (unitSmoothNorm : E → ℝ) := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => by positivity)

theorem unitSmoothNorm_hasFDerivAt (x : E) :
    HasFDerivAt unitSmoothNorm (innerSL ℝ (unitCompression x)) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).sqrt
    (by positivity : (1:ℝ)+‖x‖^2 ≠ 0)
  convert h using 1
  ext v
  simp only [unitCompression, compressionFactor, innerSL_apply, real_inner_smul_left,
    ContinuousLinearMap.smul_apply, smul_eq_mul, two_smul, ContinuousLinearMap.add_apply]
  field_simp
  ring

theorem unitSmoothNorm_fderiv : fderiv ℝ (unitSmoothNorm : E → ℝ) =
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) ∘ unitCompression :=
  funext (fun x => (unitSmoothNorm_hasFDerivAt x).fderiv)

theorem unitSmoothNorm_succ_derivative_le (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (n+1) (unitSmoothNorm : E → ℝ) x‖ ≤
      ‖iteratedFDeriv ℝ n (unitCompression : E → E) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv, unitSmoothNorm_fderiv,
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).iteratedFDeriv_comp_left
      (unitCompression_contDiff (m := n)).contDiffAt le_rfl]
  exact ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).norm_compContinuousMultilinearMap_le _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_innerSL_le ℝ))

theorem unitCompression_first_bound (x : E) :
    ‖iteratedFDeriv ℝ 1 (unitCompression : E → E) x‖ ≤ 1 := by
  rw [norm_first_derivative, (unitCompression_hasFDerivAt x).fderiv]
  exact unitCompressionDerivative_norm x

theorem unitCompression_second_bound (x : E) :
    ‖iteratedFDeriv ℝ 2 (unitCompression : E → E) x‖ ≤ 3 := by
  have heq : fderiv ℝ (unitCompression : E → E) = unitCompressionDerivative :=
    funext (fun x => (unitCompression_hasFDerivAt x).fderiv)
  have hl : LipschitzWith ⟨3, by norm_num⟩ (unitCompressionDerivative : E → E →L[ℝ] E) :=
    lipschitzWith_iff_norm_sub_le.mpr unitCompressionDerivative_sub_norm
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_first_derivative, heq]
  exact norm_fderiv_le_of_lipschitz ℝ hl

theorem unitSmoothNorm_derivative_bound {n : ℕ} (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ n (unitSmoothNorm : E → ℝ) x‖ ≤ 3 := by
  interval_cases n
  · exact (unitSmoothNorm_succ_derivative_le 0 x).trans (by
      rw [norm_iteratedFDeriv_zero]
      exact (unitCompression_norm_le_one x).trans (by norm_num))
  · exact (unitSmoothNorm_succ_derivative_le 1 x).trans
      ((unitCompression_first_bound x).trans (by norm_num))
  · exact (unitSmoothNorm_succ_derivative_le 2 x).trans (unitCompression_second_bound x)

theorem smoothNorm_radius_scaling {w : ℝ} (hw : 0 < w) (x : E) :
    smoothNorm w x = w * unitSmoothNorm (w⁻¹ • x) := by
  unfold smoothNorm unitSmoothNorm
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw]
  have heq : w^2+‖x‖^2 = w^2*(1+(w⁻¹*‖x‖)^2) := by field_simp
  rw [heq, Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hw.le]

theorem smoothNorm_contDiff {w : ℝ} (hw : 0 < w) (n : WithTop ℕ∞) :
    ContDiff ℝ n (smoothNorm w : E → ℝ) := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => by positivity)

theorem smoothNorm_derivative_bound {w : ℝ} (hw : 0 < w) {n : ℕ}
    (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ n (smoothNorm w : E → ℝ) x‖ ≤ 3*w^(1-(n:ℤ)) := by
  let A : E →L[ℝ] E := w⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ w⁻¹ := by
    dsimp only [A]
    rw [norm_smul w⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hw.le) ContinuousLinearMap.norm_id_le
  have heq : (smoothNorm w : E → ℝ) = w • ((unitSmoothNorm : E → ℝ) ∘ A) := by
    funext y
    exact smoothNorm_radius_scaling hw y
  rw [heq, iteratedFDeriv_const_smul_apply
      (((unitSmoothNorm_contDiff n).comp A.contDiff).contDiffAt),
    norm_smul w (iteratedFDeriv ℝ n ((unitSmoothNorm : E → ℝ) ∘ A) x), Real.norm_eq_abs, abs_of_pos hw,
    A.iteratedFDeriv_comp_right (unitSmoothNorm_contDiff n) x le_rfl]
  calc
    _ ≤ w*(‖iteratedFDeriv ℝ n (unitSmoothNorm : E → ℝ) (A x)‖ * ‖A‖^n) := by
      apply mul_le_mul_of_nonneg_left _ hw.le
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (unitSmoothNorm : E → ℝ) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ w*(3*(w⁻¹)^n) := by
      apply mul_le_mul_of_nonneg_left _ hw.le
      exact mul_le_mul (unitSmoothNorm_derivative_bound hn₁ hn₃ (A x))
        (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity) (by norm_num)
    _ = 3*w^(1-(n:ℤ)) := by
      rw [zpow_sub₀ hw.ne', zpow_one, zpow_natCast, div_eq_mul_inv, ← inv_pow]
      ring

theorem drive_derivative_bound {w : ℝ} (hw : 0 < w) {n : ℕ}
    (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) (c u : E) :
    ‖iteratedFDeriv ℝ n (drive w c) u‖ ≤ 48*w^(1-(n:ℤ)) := by
  change ‖iteratedFDeriv ℝ n ((16:ℝ) • (fun x => smoothNorm w (x-c))) u‖ ≤ _
  have hf : ContDiffAt ℝ n (fun x : E => smoothNorm w (x-c)) u :=
    ((smoothNorm_contDiff hw n).comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply hf,
    iteratedFDeriv_comp_sub,
    norm_smul (16:ℝ) (iteratedFDeriv ℝ n (smoothNorm w : E → ℝ) (u-c)), Real.norm_eq_abs]
  norm_num
  have h := mul_le_mul_of_nonneg_left (smoothNorm_derivative_bound hw hn₁ hn₃ (u-c))
    (by norm_num : (0:ℝ) ≤ 16)
  nlinarith

theorem publicPotential_derivative_bound {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) (u : E) :
    ‖iteratedFDeriv ℝ n (publicPotential R : E → ℝ) u‖ ≤ 48*R^(1-(n:ℤ)) := by
  have heq : (publicPotential R : E → ℝ) = fun x => drive R (0:E) x - 16*R := by
    funext x
    simp [publicPotential, drive]
    ring
  simp_rw [heq, sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' (drive_contDiff hR (0:E) n).contDiffAt contDiffAt_const]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero]
  exact drive_derivative_bound hR hn₁ hn₃ (0:E) u

end GradientHessian.LocalizedNormDerivatives
