import SampleReuse.ReverseStickThirdCalculus
import SecondOrder.RegularizedMixture

/-! Removing Bernoulli gate regularization without losing third-order bounds. -/

open SecondOrder
namespace SampleReuse
noncomputable section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem norm_iteratedFDeriv_three (f : E → ℝ) (x : E) :
    ‖iteratedFDeriv ℝ 3 f x‖ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 2),
    ← norm_iteratedFDeriv_fderiv (n := 1),
    ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]

theorem continuous_parametric_third_norm {f : P → E → ℝ}
    (hf : ContDiff ℝ 3 (Function.uncurry f)) (x : E) :
    Continuous (fun t => ‖iteratedFDeriv ℝ 3 (f t) x‖) := by
  have hfirst := contDiff_parametric_fderiv hf (show (2 : WithTop ℕ∞) + 1 ≤ 3 by decide)
  have hsecond := contDiff_parametric_fderiv (f := fun t x => fderiv ℝ (f t) x)
    hfirst (show (1 : WithTop ℕ∞) + 1 ≤ 2 by decide)
  have hthird := contDiff_parametric_fderiv (f := fun t x => fderiv ℝ (fderiv ℝ (f t)) x)
    hsecond (show (0 : WithTop ℕ∞) + 1 ≤ 1 by decide)
  have hc := hthird.continuous.comp (continuous_id.prodMk (continuous_const (y := x)))
  simpa only [norm_iteratedFDeriv_three] using hc.norm

theorem regularizedGate_second_fisher {f : E → ℝ} (hf : ContDiff ℝ 2 f) {δ ell : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (x : E)
    (hH : ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2 ≤ ell ^ 2 * f x * (1 - f x)) :
    ‖fderiv ℝ (fderiv ℝ (regularizedGate δ f)) x‖ ^ 2 ≤
      ell ^ 2 * regularizedGate δ f x * (1 - regularizedGate δ f x) := by
  rw [regularizedGate_second_fderiv hf,
    norm_smul (1 - 2 * δ) (fderiv ℝ (fderiv ℝ f) x), Real.norm_eq_abs, mul_pow, sq_abs]
  have hm := mul_le_mul_of_nonneg_left hH (sq_nonneg (1 - 2 * δ))
  have hv := regularized_gate_variance (f x) δ
  have hd : 0 ≤ ell ^ 2 * (δ * (1 - δ)) :=
    mul_nonneg (sq_nonneg ell) (mul_nonneg hδ0 (by linarith))
  unfold regularizedGate
  nlinarith [congrArg (fun t : ℝ => ell ^ 2 * t) hv]

theorem regularizedGate_iteratedFDeriv_three {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (δ : ℝ) (x : E) :
    iteratedFDeriv ℝ 3 (regularizedGate δ f) x = (1 - 2 * δ) • iteratedFDeriv ℝ 3 f x := by
  change iteratedFDeriv ℝ 3 (fun y => δ + (1 - 2 * δ) • f y) x = _
  rw [iteratedFDeriv_add_apply' contDiffAt_const (hf.contDiffAt.const_smul _),
    iteratedFDeriv_const_smul_apply' hf.contDiffAt,
    iteratedFDeriv_const_of_ne (by decide : (3 : ℕ) ≠ 0)]
  simp only [Pi.zero_apply, zero_add]

theorem regularizedGate_third_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f) {δ h : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (x : E)
    (hthird : ‖iteratedFDeriv ℝ 3 f x‖ ≤ h) :
    ‖iteratedFDeriv ℝ 3 (regularizedGate δ f) x‖ ≤ h := by
  rw [regularizedGate_iteratedFDeriv_three hf,
    norm_smul (1 - 2 * δ) (iteratedFDeriv ℝ 3 f x), Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * δ)]
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ 3 f x‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ h := by simpa only [one_mul] using hthird

variable {ι : Type*} [Fintype ι]

theorem regularizedMixture_continuous_third (p : ι → E → ℝ)
    (V : (ι → Bool) → E → ℝ) (hp : ∀ i, ContDiff ℝ 3 (p i))
    (hV : ∀ ω, ContDiff ℝ 3 (V ω)) (x : E) :
    Continuous (fun δ : ℝ => ‖iteratedFDeriv ℝ 3 (regularizedMixture p V δ) x‖) :=
  continuous_parametric_third_norm (regularizedMixture_joint_contDiff p V hp hV) x

end
end SampleReuse
