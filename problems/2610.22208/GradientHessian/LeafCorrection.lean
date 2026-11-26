import GradientHessian.LeafCutoff

/-! Actual uniform tensor bounds for the capped quadratic correction, with
the matrix norm and cap radius factored out explicitly. -/

namespace GradientHessian.LeafCorrection
open LeafCutoff RadialHigherDerivatives
open Set Filter
open scoped Topology BigOperators InnerProductSpace
noncomputable section

def correctionConstant (n : ℕ) : ℝ :=
  1+8*(∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*cutoffConstant i*2^(n-i))

theorem correctionConstant_pos (n : ℕ) : 0 < correctionConstant n := by
  have hs : 0 ≤ ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*cutoffConstant i*2^(n-i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (cutoffConstant_pos i).le) (by positivity))
  unfold correctionConstant
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def quadratic (C : E →L[ℝ] E) (y : E) : ℝ := ⟪y,C y⟫_ℝ
def correction (L : ℝ) (C : E →L[ℝ] E) (y : E) : ℝ := (1/2)*cutoff L y*quadratic C y

theorem quadratic_contDiff (C : E →L[ℝ] E) (n : ℕ) : ContDiff ℝ n (quadratic C) :=
  contDiff_id.inner ℝ C.contDiff

theorem correction_contDiff {L : ℝ} (hL : 0 < L) (C : E →L[ℝ] E) :
    ContDiff ℝ 3 (correction L C) :=
  (contDiff_const.mul (cutoff_contDiff hL)).mul (quadratic_contDiff C 3)

theorem linear_derivative_ball (C : E →L[ℝ] E) (n : ℕ) {y : E} (hy : ‖y‖ ≤ 4) :
    ‖iteratedFDeriv ℝ n C y‖ ≤ 4*‖C‖ := by
  cases n with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact (C.le_opNorm y).trans (by nlinarith [norm_nonneg C])
  | succ n =>
    exact (norm_iteratedFDeriv_linear_succ_le C n y).trans (by nlinarith [norm_nonneg C])

theorem quadratic_derivative_ball (C : E →L[ℝ] E) (n : ℕ) {y : E} (hy : ‖y‖ ≤ 4) :
    ‖iteratedFDeriv ℝ n (quadratic C) y‖ ≤ 16*2^n*‖C‖ := by
  have h := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (show ContDiff ℝ n (id : E → E) from contDiff_id) C.contDiff y le_rfl (norm_innerSL_le ℝ)
  have hsum : (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)) = 2^n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*
        ‖iteratedFDeriv ℝ j (id : E → E) y‖*‖iteratedFDeriv ℝ (n-j) C y‖ := h
    _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*4*(4*‖C‖) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_id_le_four j hy) (Nat.cast_nonneg _))
        (linear_derivative_ball C (n-j) hy) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]; ring

theorem correction_one_derivative_bound (C : E →L[ℝ] E) (n : ℕ) (hn : n ≤ 3) (y : E) :
    ‖iteratedFDeriv ℝ n (correction 1 C) y‖ ≤ correctionConstant n*‖C‖ := by
  by_cases hy : ‖y‖ ≤ 4
  · have hmul := norm_iteratedFDeriv_mul_le cutoff_one_contDiff (quadratic_contDiff C 3)
      y (by exact_mod_cast hn)
    have he : correction 1 C = (1/2:ℝ) • (fun z => cutoff 1 z*quadratic C z) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, correction]
      ring
    rw [he, iteratedFDeriv_const_smul_apply
      ((cutoff_one_contDiff.mul (quadratic_contDiff C 3)).of_le (by exact_mod_cast hn)).contDiffAt,
      norm_smul (1/2:ℝ) (iteratedFDeriv ℝ n (fun z => cutoff 1 z*quadratic C z) y)]
    norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    calc
      _ ≤ (1/2:ℝ)*(∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*
          ‖iteratedFDeriv ℝ i (cutoff 1 : E → ℝ) y‖*‖iteratedFDeriv ℝ (n-i) (quadratic C) y‖) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ ≤ (1/2:ℝ)*(∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*
          cutoffConstant i*(16*2^(n-i)*‖C‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (cutoff_one_derivative_bound i
            ((Finset.mem_range_succ_iff.mp hi).trans hn) y) (Nat.cast_nonneg _))
          (quadratic_derivative_ball C (n-i) hy) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (cutoffConstant_pos i).le)
      _ ≤ _ := by
        have he : (∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*cutoffConstant i*(16*2^(n-i)*‖C‖)) =
            16*‖C‖*(∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*cutoffConstant i*2^(n-i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [he]
        unfold correctionConstant
        nlinarith [norm_nonneg C]
  · have he : correction 1 C =ᶠ[𝓝 y] (fun _ => 0) := by
      have hnear : ∀ᶠ z : E in 𝓝 y, 4 < ‖z‖ :=
        continuous_norm.continuousAt.eventually (lt_mem_nhds (lt_of_not_ge hy))
      filter_upwards [hnear] with z hz
      simp [correction, cutoff_zero (by norm_num : (0:ℝ) < 1) (by linarith : 2*1 ≤ ‖z‖)]
    rw [iteratedFDeriv_eq_of_eventuallyEq he n, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact mul_nonneg (correctionConstant_pos n).le (norm_nonneg C)

theorem correction_scaling {L : ℝ} (hL : 0 < L) (C : E →L[ℝ] E) (y : E) :
    correction L C y = L^2*correction 1 C (L⁻¹ • y) := by
  unfold correction quadratic
  rw [← cutoff_scaling hL]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  field_simp
  ring

theorem correction_derivative_bound {L : ℝ} (hL : 0 < L) (C : E →L[ℝ] E)
    (n : ℕ) (hn : n ≤ 3) (y : E) :
    ‖iteratedFDeriv ℝ n (correction L C) y‖ ≤ correctionConstant n*‖C‖*L^2/L^n := by
  let A : E →L[ℝ] E := L⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ L⁻¹ := by
    dsimp only [A]
    rw [norm_smul L⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hL.le) ContinuousLinearMap.norm_id_le
  have he : correction L C = (L^2:ℝ) • (correction 1 C ∘ A) := funext (correction_scaling hL C)
  rw [he, iteratedFDeriv_const_smul_apply
    (((correction_contDiff (by norm_num : (0:ℝ) < 1) C).comp A.contDiff).of_le
      (by exact_mod_cast hn)).contDiffAt,
    norm_smul (L^2:ℝ) (iteratedFDeriv ℝ n (correction 1 C ∘ A) y),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg L),
    A.iteratedFDeriv_comp_right (correction_contDiff (by norm_num) C) y (by exact_mod_cast hn)]
  calc
    _ ≤ L^2*(‖iteratedFDeriv ℝ n (correction 1 C) (A y)‖*‖A‖^n) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (correction 1 C) (A y)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ L^2*((correctionConstant n*‖C‖)*(L⁻¹)^n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (correction_one_derivative_bound C n hn _)
        (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity)
        (mul_nonneg (correctionConstant_pos n).le (norm_nonneg C))) (sq_nonneg L)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring

end
end GradientHessian.LeafCorrection
