import GradientHessian.SelectorProfileBounds
import GradientHessian.LatchLocalDerivatives
import GradientHessian.LocalizedProductDerivatives

/-! Endpoint-relative bounds for the actual scaled selector port. Centering
the scalar profile permits the composition bound to retain its variance factor,
including at both flat endpoints. -/

namespace GradientHessian.SelectorPortBounds
open Profiles LatchChain LatchActivation LatchLocalDerivatives SelectorProfileBounds
  LocalizedProductDerivatives
noncomputable section

theorem centered_scalar_bound (a : ℝ) {i : ℕ} (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (fun t => varpi t - varpi a) a‖ ≤
      60480 * varianceRoot (varpi a) := by
  have hv : 0 ≤ varianceRoot (varpi a) := Real.sqrt_nonneg _
  by_cases hi0 : i = 0
  · subst i
    simp only [norm_iteratedFDeriv_zero, sub_self, norm_zero]
    positivity
  have hf : ContDiff ℝ i varpi := contDiff_varpi.of_le (by exact_mod_cast hi.trans (by norm_num : 2 ≤ 3))
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_const_of_pos (by omega) hf.contDiffAt,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  interval_cases i
  · exact False.elim (hi0 rfl)
  · simpa only [iteratedDeriv_one] using
      (varpi_first_relative a).trans (by nlinarith : 1680 * varianceRoot (varpi a) ≤ 60480 * varianceRoot (varpi a))
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one] using varpi_second_relative a

def portConstant : ℝ := 1 + localConstant 3 + 60480 * readoutConstant + 120960 * readoutConstant ^ 2

theorem portConstant_ge_one : 1 ≤ portConstant := by
  have hloc := localConstant_pos 3
  have hr := readoutConstant_ge_one
  unfold portConstant
  nlinarith [sq_nonneg readoutConstant]

theorem portConstant_ge_third : localConstant 3 ≤ portConstant := by
  have hr := readoutConstant_ge_one
  unfold portConstant
  nlinarith [sq_nonneg readoutConstant]

theorem relative_coefficient_bound {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2) :
    n.factorial * 60480 * readoutConstant ^ n ≤ portConstant := by
  have hloc := localConstant_pos 3
  have hr := readoutConstant_ge_one
  unfold portConstant
  interval_cases n <;> norm_num [Nat.factorial] <;> nlinarith [sq_nonneg readoutConstant]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def port (R : ℝ) (v x : E) : ℝ := varpi (u R v x)

theorem port_contDiff (R : ℝ) (v : E) : ContDiff ℝ 3 (port R v) :=
  contDiff_varpi.comp (u_contDiff R v)

theorem unscaled_relative_bound (v x : E) (hv : ‖v‖ = 1)
    {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y => varpi (readout v y)) x‖ ≤
      portConstant * varianceRoot (varpi (readout v x)) := by
  let g := fun t : ℝ => varpi t - varpi (readout v x)
  have hg : ContDiff ℝ 3 g := contDiff_varpi.sub contDiff_const
  have h := norm_iteratedFDeriv_comp_le hg (readout_contDiff v)
    (by exact_mod_cast hn2.trans (by norm_num : 2 ≤ 3)) x
    (fun i hi => centered_scalar_bound (readout v x) (hi.trans hn2))
    (fun i hi hin => readout_derivative_bound v x hv hi (hin.trans hn2 |>.trans (by norm_num : 2 ≤ 3)))
  have he : g ∘ readout v = fun y => varpi (readout v y) + -varpi (readout v x) := by
    rfl
  have hf : ContDiff ℝ n (fun y => varpi (readout v y)) :=
    (contDiff_varpi.comp (readout_contDiff v)).of_le
      (by exact_mod_cast hn2.trans (by norm_num : 2 ≤ 3))
  rw [he, iteratedFDeriv_add_const_of_pos (f := fun y => varpi (readout v y)) hn1
    hf.contDiffAt] at h
  apply h.trans
  have hc := mul_le_mul_of_nonneg_right (relative_coefficient_bound hn1 hn2)
    (Real.sqrt_nonneg (varpi (readout v x) * (1 - varpi (readout v x))))
  change n.factorial * 60480 * readoutConstant ^ n * varianceRoot (varpi (readout v x)) ≤
    portConstant * varianceRoot (varpi (readout v x)) at hc
  convert hc using 1; ring

theorem port_relative_bound {R : ℝ} (hR : 0 < R) (v x : E) (hv : ‖v‖ = 1)
    {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (port R v) x‖ ≤
      portConstant * varianceRoot (port R v x) / R ^ n := by
  let A : E →L[ℝ] E := R⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ R⁻¹ := by
    dsimp only [A]
    rw [norm_smul R⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hR.le) ContinuousLinearMap.norm_id_le
  have hf : ContDiff ℝ 3 (fun y => varpi (readout v y)) :=
    contDiff_varpi.comp (readout_contDiff v)
  change ‖iteratedFDeriv ℝ n ((fun y => varpi (readout v y)) ∘ A) x‖ ≤ _
  rw [A.iteratedFDeriv_comp_right hf x (by exact_mod_cast hn2.trans (by norm_num : 2 ≤ 3))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun y => varpi (readout v y)) (A x)‖ * ‖A‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (fun y => varpi (readout v y)) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ (portConstant * varianceRoot (varpi (readout v (A x)))) * (R⁻¹) ^ n :=
      mul_le_mul (unscaled_relative_bound v (A x) hv hn1 hn2)
        (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity)
        (mul_nonneg (zero_le_one.trans portConstant_ge_one) (Real.sqrt_nonneg _))
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; rfl

theorem port_third_bound {R : ℝ} (hR : 0 < R) (v x : E) (hv : ‖v‖ = 1) :
    ‖iteratedFDeriv ℝ 3 (port R v) x‖ ≤ portConstant / R ^ 3 := by
  have h : ‖iteratedFDeriv ℝ 3 (port R v) x‖ ≤ localConstant 3 / R ^ 3 := by
    simpa [port, scalarProfile] using
      scaled_composite_derivative_bound (3 : Fin 4) hR v x hv (n := 3) (by norm_num)
  exact h.trans (div_le_div_of_nonneg_right portConstant_ge_third (pow_nonneg hR.le 3))

end
end GradientHessian.SelectorPortBounds
