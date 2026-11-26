import GradientHessian.LeafCorrection
import GradientHessian.InverseGateFunctions
import GradientHessian.InverseGateOperator

/-! The actual capped numerical quadratic and its coercive gradient matrix.
All bounds use operator norms on the original Hilbert space. -/

noncomputable section
namespace GradientHessian.LeafNumerical
open LeafCutoff
open Filter Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def deviation (M : ℝ) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  A - (2*M) • ContinuousLinearMap.id ℝ E

def base (M L : ℝ) (A : E →L[ℝ] E) (y : E) : ℝ :=
  M*‖y‖^2 + LeafCorrection.correction L (deviation M A) y

def radialCoefficient (L : ℝ) (C : E →L[ℝ] E) (y : E) : ℝ :=
  deriv (radial L) ‖y‖ / (2*‖y‖) * ⟪y,C y⟫_ℝ

def gradientMatrix (M L : ℝ) (A : E →L[ℝ] E) (y : E) : E →L[ℝ] E :=
  (2*M) • ContinuousLinearMap.id ℝ E + cutoff L y • deviation M A +
    radialCoefficient L (deviation M A) y • ContinuousLinearMap.id ℝ E

theorem deviation_symmetric (M : ℝ) (A : E →L[ℝ] E)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) :
    ∀ x z, ⟪deviation M A x,z⟫_ℝ = ⟪x,deviation M A z⟫_ℝ := by
  intro x z
  simp only [deviation, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hsym]

theorem deviation_norm {M : ℝ} (hM : 0 ≤ M) (A : E →L[ℝ] E) (hA : ‖A‖ ≤ M) :
    ‖deviation M A‖ ≤ 3*M := by
  have hid : ‖(2*M) • ContinuousLinearMap.id ℝ E‖ ≤ 2*M := by
    rw [norm_smul (2*M) (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2*M)]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  exact (norm_sub_le _ _).trans (by linarith)

theorem deviation_nonpos {M : ℝ} (hM : 0 ≤ M) (A : E →L[ℝ] E)
    (hA : ‖A‖ ≤ M) (y : E) : ⟪y,deviation M A y⟫_ℝ ≤ 0 := by
  have h := (real_inner_le_norm y (A y)).trans
    (mul_le_mul_of_nonneg_left ((A.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg y))) (norm_nonneg y))
  simp only [deviation, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg hM (sq_nonneg ‖y‖)]

theorem radialCoefficient_nonneg {L M : ℝ} (hL : 0 < L) (hM : 0 ≤ M)
    (A : E →L[ℝ] E) (hA : ‖A‖ ≤ M) (y : E) :
    0 ≤ radialCoefficient L (deviation M A) y :=
  mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (radial_derivative_nonpos hL _) (by positivity))
    (deviation_nonpos hM A hA y)

theorem base_mixture (M L : ℝ) (A : E →L[ℝ] E) (y : E) :
    base M L A y = (1-cutoff L y)*M*‖y‖^2 +
      cutoff L y * InverseGate.quadratic A y := by
  simp only [base, LeafCorrection.correction, LeafCorrection.quadratic, deviation,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, InverseGate.quadratic]
  ring

theorem radialCoefficient_bound {L : ℝ} (hL : 0 < L) (C : E →L[ℝ] E) (y : E) :
    |radialCoefficient L C y| ≤ (35/16)*‖C‖ := by
  by_cases hy : y = 0
  · subst y
    simp [radialCoefficient]
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hq : |⟪y,C y⟫_ℝ| ≤ ‖C‖*‖y‖^2 := by
    calc
      _ ≤ ‖y‖*‖C y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖y‖*(‖C‖*‖y‖) := mul_le_mul_of_nonneg_left (C.le_opNorm y) hr.le
      _ = _ := by ring
  by_cases hrL : ‖y‖ ≤ 2*L
  · calc
      _ = |deriv (radial L) ‖y‖|/(2*‖y‖)*|⟪y,C y⟫_ℝ| := by
        rw [radialCoefficient, abs_mul, abs_div, abs_of_pos (by positivity : 0 < 2*‖y‖)]
      _ ≤ |deriv (radial L) ‖y‖|/(2*‖y‖)*(‖C‖*‖y‖^2) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = |deriv (radial L) ‖y‖| *‖C‖*‖y‖/2 := by field_simp; ring
      _ ≤ ((35/16)/L)*‖C‖*(2*L)/2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_right (radial_derivative_bound hL _) (norm_nonneg C))
            hrL hr.le (by positivity)) (by norm_num)
      _ = _ := by field_simp; ring
  · have ha : 1 < ‖y‖/L-1 := by
      have h := (lt_div_iff₀ hL).mpr (lt_of_not_ge hrL)
      linarith
    have hd : deriv (radial L) ‖y‖ = 0 := by
      rw [(radial_derivative L ‖y‖).deriv]
      simp [Profiles.step₁, not_le.mpr (show 0 < ‖y‖/L-1 by linarith), not_le.mpr ha]
    simp only [radialCoefficient, hd, zero_div, zero_mul, abs_zero]
    positivity

theorem gradientMatrix_norm {M L : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    (A : E →L[ℝ] E) (hA : ‖A‖ ≤ M) (y : E) :
    ‖gradientMatrix M L A y‖ ≤ 12*M := by
  have hC := deviation_norm hM A hA
  have hθ := cutoff_bounds L y
  have hα := radialCoefficient_bound hL (deviation M A) y
  have hid (c : ℝ) : ‖c • ContinuousLinearMap.id ℝ E‖ ≤ |c| := by
    rw [norm_smul c (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hc : ‖cutoff L y • deviation M A‖ ≤ ‖deviation M A‖ := by
    rw [norm_smul (cutoff L y) (deviation M A), Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ.2
  calc
    _ ≤ ‖(2*M) • ContinuousLinearMap.id ℝ E‖ + ‖cutoff L y • deviation M A‖ +
      ‖radialCoefficient L (deviation M A) y • ContinuousLinearMap.id ℝ E‖ := norm_add₃_le
    _ ≤ 2*M + ‖deviation M A‖ + (35/16)*‖deviation M A‖ := by
      exact add_le_add (add_le_add
        ((hid (2*M)).trans_eq (abs_of_nonneg (by positivity))) hc) ((hid _).trans hα)
    _ ≤ 12*M := by nlinarith

theorem gradientMatrix_symmetric (M L : ℝ) (A : E →L[ℝ] E)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (y : E) :
    ∀ x z, ⟪gradientMatrix M L A y x,z⟫_ℝ = ⟪x,gradientMatrix M L A y z⟫_ℝ := by
  intro x z
  simp only [gradientMatrix, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, deviation_symmetric M A hsym x z]

theorem base_lower {M : ℝ} (hM : 1 ≤ M) (L : ℝ) (A : E →L[ℝ] E)
    (hA : InverseGate.LowerBound A) (y : E) : ‖y‖^2/2 ≤ base M L A y := by
  have hθ := cutoff_bounds L y
  have hq : ‖y‖^2/2 ≤ InverseGate.quadratic A y := by
    have h := hA y
    rw [real_inner_comm] at h
    unfold InverseGate.quadratic
    linarith
  rw [base_mixture]
  have h1 := mul_le_mul_of_nonneg_left hq hθ.1
  have h2 := mul_le_mul_of_nonneg_left
    (show ‖y‖^2/2 ≤ M*‖y‖^2 by nlinarith [sq_nonneg ‖y‖])
    (sub_nonneg.mpr hθ.2)
  nlinarith

theorem gradientMatrix_lower {M L : ℝ} (hM : 1 ≤ M) (hL : 0 < L)
    (A : E →L[ℝ] E) (hA : InverseGate.LowerBound A) (hAn : ‖A‖ ≤ M) (y : E) :
    InverseGate.LowerBound (gradientMatrix M L A y) := by
  intro z
  have hθ := cutoff_bounds L y
  have hα := radialCoefficient_nonneg hL (by linarith : 0 ≤ M) A hAn y
  have h1 := mul_le_mul_of_nonneg_left (hA z) hθ.1
  have h2 := mul_nonneg (sub_nonneg.mpr hθ.2)
    (mul_nonneg (show 0 ≤ 2*M-1 by linarith) (sq_nonneg ‖z‖))
  have h3 := mul_nonneg hα (sq_nonneg ‖z‖)
  simp only [deviation] at h3
  simp only [gradientMatrix, deviation, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith

theorem localization (B : E →L[ℝ] E) (hB : InverseGate.LowerBound B)
    (y f : E) {C ε : ℝ} (hf : ‖f‖ ≤ C) (hg : ‖B y+f‖ ≤ ε) : ‖y‖ ≤ ε+C := by
  have h := norm_sub_le (B y+f) f
  rw [add_sub_cancel_right] at h
  exact (InverseGate.lowerBound_norm B hB y).trans (h.trans (add_le_add hg hf))

theorem convex_matrix_lower {ι : Type*} [Fintype ι] (w : ι → ℝ) (q M : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : 0 ≤ q) (hsum : q + ∑ i, w i = 1) (hM : 1 ≤ M)
    (B : ι → E →L[ℝ] E) (hB : ∀ i, InverseGate.LowerBound (B i)) :
    InverseGate.LowerBound ((q*(2*M)) • ContinuousLinearMap.id ℝ E + ∑ i, w i • B i) := by
  intro y
  have hs : (∑ i, w i)*‖y‖^2 ≤ ∑ i, w i*⟪B i y,y⟫_ℝ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hB i y) (hw i))
  have hq' : q*‖y‖^2 ≤ q*(2*M)*‖y‖^2 := by
    nlinarith [mul_nonneg hq (sq_nonneg ‖y‖),
      mul_nonneg (mul_nonneg hq (show 0 ≤ 2*M-1 by linarith)) (sq_nonneg ‖y‖)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.sum_apply, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, sum_inner]
  nlinarith

theorem convex_force_bound {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) (f : ι → E) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) : ‖∑ i, w i • f i‖ ≤ C := by
  calc
    _ ≤ ∑ i, ‖w i • f i‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i*C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (hf i) (hw i)
    _ = (∑ i, w i)*C := by rw [Finset.sum_mul]
    _ ≤ C := mul_le_of_le_one_left hC hsum

variable [CompleteSpace E]

theorem cutoff_hasGradientAt {L : ℝ} (hL : 0 < L) (y : E) :
    HasGradientAt (cutoff L) ((deriv (radial L) ‖y‖ / ‖y‖) • y) y := by
  by_cases hy : y = 0
  · subst y
    simp only [smul_zero]
    apply (hasGradientAt_const (0 : E) (1 : ℝ)).congr_of_eventuallyEq
    have hn : ∀ᶠ z : E in 𝓝 (0:E), ‖z‖ < L :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using hL))
    filter_upwards [hn] with z hz
    exact cutoff_one hL hz.le
  · have h := ((radial_derivative L ‖y‖).comp_hasFDerivAt y
      (RadialSquash.norm_hasFDerivAt hy))
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext z
    simp only [InnerProductSpace.toDual_apply, real_inner_smul_left,
      ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul]
    rw [(radial_derivative L ‖y‖).deriv]
    ring

theorem base_hasGradientAt {M L : ℝ} (hL : 0 < L) (A : E →L[ℝ] E)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (y : E) :
    HasGradientAt (base M L A) (gradientMatrix M L A y y) y := by
  have hq := (InverseGate.quadratic_hasGradientAt (deviation M A)
    (deviation_symmetric M A hsym) y).hasFDerivAt
  have hc := (cutoff_hasGradientAt hL y).hasFDerivAt
  have hb := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul M
  have h := hb.add (hc.mul hq)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · funext z
    simp only [base, LeafCorrection.correction, LeafCorrection.quadratic,
      InverseGate.quadratic]
    ring
  · ext z
    simp only [gradientMatrix, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply, inner_add_left,
      real_inner_smul_left, smul_eq_mul, innerSL_apply, two_smul,
      radialCoefficient, InverseGate.quadratic]
    ring

theorem base_gradient {M L : ℝ} (hL : 0 < L) (A : E →L[ℝ] E)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (y : E) :
    gradient (base M L A) y = gradientMatrix M L A y y :=
  (base_hasGradientAt hL A hsym y).gradient

end GradientHessian.LeafNumerical
