import GradientHessian.RadialSquash
import GradientHessian.JetLocality
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Literal numerical-gate scalar functions and their actual derivatives. -/

noncomputable section
namespace GradientHessian.InverseGate

open Filter
open scoped Topology InnerProductSpace

def H₀ : ℝ := 2 ^ 20
def alpha : ℝ := H₀ / 32
def B₀ : ℝ := 16 * H₀

theorem H₀_pos : 0 < H₀ := by norm_num [H₀]
theorem alpha_pos : 0 < alpha := by norm_num [alpha, H₀]
theorem B₀_pos : 0 < B₀ := by norm_num [B₀, H₀]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def forcingArg (b y : E) : ℝ := ⟪b, y⟫_ℝ / H₀ ^ 2
def forcing (b y : E) : ℝ := H₀ ^ 2 * (10 + IntegralProfiles.theta (forcingArg b y))
def gateArg (a y : E) : ℝ := ⟪a, RadialSquash.squash B₀ y⟫_ℝ / alpha
def gate (a y : E) : ℝ := Profiles.chi (gateArg a y)
def quadratic (A : E →L[ℝ] E) (y : E) : ℝ := (1 / 2) * ⟪y, A y⟫_ℝ
def g (A : E →L[ℝ] E) (b y : E) : ℝ := quadratic A y - forcing b y
def objective (A : E →L[ℝ] E) (b a : E) (d : ℝ) (y : E) : ℝ :=
  g A b y - d * gate a y

theorem forcing_hasGradientAt (b y : E) :
    HasGradientAt (forcing b) ((deriv IntegralProfiles.theta (forcingArg b y)) • b) y := by
  have hi := (innerSL ℝ b).hasFDerivAt (x := y)
  have ha := hi.mul_const ((H₀ ^ 2)⁻¹)
  simp only [← div_eq_mul_inv] at ha
  have ht := (IntegralProfiles.theta_derivative (forcingArg b y)).differentiableAt.hasDerivAt
  have h := ((ht.comp_hasFDerivAt y ha).const_add 10).const_mul (H₀ ^ 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext z
  simp [InnerProductSpace.toDual_apply, real_inner_smul_left, H₀]
  ring

theorem forcing_gradient_norm_le (b y : E) : ‖gradient (forcing b) y‖ ≤ ‖b‖ := by
  rw [(forcing_hasGradientAt b y).gradient, norm_smul, Real.norm_eq_abs]
  have h := IntegralProfiles.theta_derivative_bounds (forcingArg b y)
  rw [abs_of_nonneg h.1]
  nlinarith [norm_nonneg b]

omit [CompleteSpace E] in
theorem gateArg_contDiff (a : E) : ContDiff ℝ 4 (gateArg a) :=
  ((innerSL ℝ a).contDiff.comp (RadialSquash.squash_contDiff B₀_pos)).div_const alpha

omit [CompleteSpace E] in
theorem gate_contDiff (a : E) : ContDiff ℝ 3 (gate a) :=
  Profiles.contDiff_chi.comp ((gateArg_contDiff a).of_le (by decide : (3 : WithTop ℕ∞) ≤ 4))

omit [CompleteSpace E] in
theorem gate_hasFDerivAt (a y : E) :
    HasFDerivAt (gate a)
      ((deriv Profiles.chi (gateArg a y) / alpha) •
        ((innerSL ℝ a).comp (fderiv ℝ (RadialSquash.squash B₀) y))) y := by
  have hR := (RadialSquash.squash_contDiff B₀_pos).differentiable (by norm_num) y
  have hi := (innerSL ℝ a).hasFDerivAt.comp y hR.hasFDerivAt
  have ha := hi.mul_const alpha⁻¹
  simp only [← div_eq_mul_inv] at ha
  have hc := (Profiles.chi_derivative (gateArg a y)).differentiableAt.hasDerivAt
  have h := hc.comp_hasFDerivAt y ha
  convert h using 1
  ext z
  simp [div_eq_mul_inv]
  ring

theorem gate_gradient_norm_le (a y : E) (ha : ‖a‖ = 1) :
    ‖gradient (gate a) y‖ ≤ 12 / alpha := by
  have hnorm : ‖gradient (gate a) y‖ = ‖fderiv ℝ (gate a) y‖ := by
    simp [gradient]
  rw [hnorm, (gate_hasFDerivAt a y).fderiv]
  rw [norm_smul (deriv Profiles.chi (gateArg a y) / alpha)
    ((innerSL ℝ a).comp (fderiv ℝ (RadialSquash.squash B₀) y)), Real.norm_eq_abs, abs_div,
    abs_of_pos alpha_pos]
  have hcomp := ContinuousLinearMap.opNorm_comp_le (innerSL ℝ a)
    (fderiv ℝ (RadialSquash.squash B₀) y)
  rw [innerSL_apply_norm, ha, one_mul] at hcomp
  have h1 : ‖(innerSL ℝ a).comp (fderiv ℝ (RadialSquash.squash B₀) y)‖ ≤ 1 :=
    hcomp.trans (RadialSquash.squash_fderiv_norm_le B₀_pos y)
  have h2 := div_le_div_of_nonneg_right (Profiles.chi_derivative_bound (gateArg a y)) alpha_pos.le
  have hh := mul_le_mul h2 h1 (norm_nonneg _)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 12) alpha_pos.le)
  simpa only [mul_one] using hh

theorem quadratic_hasGradientAt (A : E →L[ℝ] E)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ) (y : E) :
    HasGradientAt (quadratic A) (A y) y := by
  have h := ((hasFDerivAt_id y).inner ℝ (A.hasFDerivAt (x := y))).const_mul (1 / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext z
  simp only [InnerProductSpace.toDual_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    fderivInnerCLM_apply, id_eq]
  rw [← hsym y z, real_inner_comm z (A y)]
  ring

theorem objective_hasGradientAt (A : E →L[ℝ] E)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ) (b a y : E) (d : ℝ) :
    HasGradientAt (objective A b a d)
      (A y - gradient (forcing b) y - d • gradient (gate a) y) y := by
  have hf := (forcing_hasGradientAt b y).differentiableAt.hasGradientAt.hasFDerivAt
  have hc := ((gate_contDiff a).differentiable (by norm_num) y).hasGradientAt.hasFDerivAt
  have h := ((quadratic_hasGradientAt A hsym y).hasFDerivAt.sub hf).sub (hc.const_mul d)
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [objective, g, map_sub, map_smul] using h

omit [CompleteSpace E] in
theorem gate_local_identity (a y : E) (hy : ‖y‖ < B₀) :
    gate a =ᶠ[𝓝 y] (fun x => Profiles.chi (⟪a, x⟫_ℝ / alpha)) := by
  have hn : ∀ᶠ x : E in 𝓝 y, ‖x‖ < B₀ :=
    continuous_norm.continuousAt.preimage_mem_nhds (gt_mem_nhds hy)
  filter_upwards [hn] with x hx
  change Profiles.chi (⟪a, RadialSquash.squash B₀ x⟫_ℝ / alpha) = _
  rw [RadialSquash.squash_identity B₀_pos hx.le]

theorem gate_hasGradientAt_inside (a y : E) (hy : ‖y‖ < B₀) :
    HasGradientAt (gate a) ((deriv Profiles.chi (⟪a, y⟫_ℝ / alpha) / alpha) • a) y := by
  have hi := ((innerSL ℝ a).hasFDerivAt (x := y)).mul_const alpha⁻¹
  simp only [← div_eq_mul_inv] at hi
  have hc := (Profiles.chi_derivative (⟪a, y⟫_ℝ / alpha)).differentiableAt.hasDerivAt
  have h := hc.comp_hasFDerivAt y hi
  have hg : HasGradientAt (fun x => Profiles.chi (⟪a, x⟫_ℝ / alpha))
      ((deriv Profiles.chi (⟪a, y⟫_ℝ / alpha) / alpha) • a) y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext z
    simp [InnerProductSpace.toDual_apply, real_inner_smul_left, div_eq_mul_inv]
    ring
  exact hg.congr_of_eventuallyEq (gate_local_identity a y hy)

theorem chi_derivative_nonneg (t : ℝ) : 0 ≤ deriv Profiles.chi t := by
  rw [(Profiles.chi_derivative t).deriv]
  have h := (Profiles.derivative_bounds (4 * t - 1)).1
  rw [Profiles.deriv_step] at h
  positivity

omit [CompleteSpace E] in
theorem gate_flat_near_of_argument (a y : E) (hy : ‖y‖ < B₀)
    (harg : 1 / 2 < ⟪a, y⟫_ℝ / alpha) : gate a =ᶠ[𝓝 y] fun _ => 1 := by
  have hc : ContinuousAt (fun x => ⟪a, x⟫_ℝ / alpha) y :=
    (innerSL ℝ a).continuous.continuousAt.div_const alpha
  filter_upwards [gate_local_identity a y hy, hc.preimage_mem_nhds (lt_mem_nhds harg)] with x hx ha
  rw [hx]
  exact Profiles.chi_one (le_of_lt ha)

end GradientHessian.InverseGate
