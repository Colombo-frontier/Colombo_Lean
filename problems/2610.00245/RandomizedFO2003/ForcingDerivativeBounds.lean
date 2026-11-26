import RandomizedFO2003.CascadeForcing
import RandomizedFO2003.DerivativeComposition

namespace RandomizedFO2003.Primitives

/-- Positive-order bounds for saturation, including the sharp first-order
bound. The constants are independent of the saturation threshold. -/
noncomputable def saturationDerivativeConstant (n : ℕ) : ℝ :=
  if hn : 2 ≤ n then (saturation_derivative_bound n hn).choose else 1

theorem saturationDerivativeConstant_pos (n : ℕ) : 0 < saturationDerivativeConstant n := by
  unfold saturationDerivativeConstant
  split_ifs with hn
  · exact (saturation_derivative_bound n hn).choose_spec.1
  · exact zero_lt_one

theorem saturationDerivativeConstant_spec (n : ℕ) (hn : 1 ≤ n) {K : ℝ} (hK : 0 ≤ K) (x : ℝ) :
    |iteratedDeriv n (saturation K) x| ≤ saturationDerivativeConstant n := by
  unfold saturationDerivativeConstant
  split_ifs with htwo
  · exact (saturation_derivative_bound n htwo).choose_spec.2 K x
  · have hn1 : n = 1 := by omega
    subst n
    simpa only [iteratedDeriv_one] using saturation_deriv_bound hK x

end RandomizedFO2003.Primitives

namespace RandomizedFO2003.Cascade

open Primitives Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def forcingReadoutLinear (b : E) (D : ℝ) : E →L[ℝ] ℝ := D⁻¹ • innerSL ℝ b

@[simp] theorem forcingReadoutLinear_apply (b : E) (D : ℝ) (x : E) :
    forcingReadoutLinear b D x = forcingReadout b D x := by
  simp only [forcingReadoutLinear, ContinuousLinearMap.smul_apply, innerSL_apply,
    smul_eq_mul, forcingReadout, div_eq_mul_inv, mul_comm]

theorem forcingReadoutLinear_norm (b : E) {D : ℝ} (hD : 0 < D) :
    ‖forcingReadoutLinear b D‖ = ‖b‖ / D := by
  rw [forcingReadoutLinear, norm_smul D⁻¹ (innerSL ℝ b), norm_inv, Real.norm_eq_abs, abs_of_pos hD,
    innerSL_apply_norm, div_eq_mul_inv, mul_comm]

/-- All positive derivatives of the actual bounded forcing term have the
expected scale. In particular, orders two and three are bounded by constant
multiples of `‖b‖²/D` and `‖b‖³/D²`, independently of dimension and offset. -/
theorem forcing_iteratedFDeriv_bound (n : ℕ) (hn : 1 ≤ n) (b : E)
    {D K : ℝ} (hD : 0 < D) (hK : 0 ≤ K) (C₀ : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ n (forcing b D C₀ K) x‖ ≤
      D * saturationDerivativeConstant n * (‖b‖ / D) ^ n := by
  let f : ℝ → ℝ := fun q => C₀ + saturation K q
  have hf : ContDiff ℝ n f := contDiff_const.add (saturation_contDiff K n)
  have hscalar (q : ℝ) : ‖iteratedFDeriv ℝ n f q‖ ≤ saturationDerivativeConstant n := by
    rw [show f = fun y => C₀ + saturation K y from rfl,
      iteratedFDeriv_const_add n hn C₀ (saturation_contDiff K n) q,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact saturationDerivativeConstant_spec n hn hK q
  have hcomp := norm_iteratedFDeriv_comp_linear_le (forcingReadoutLinear b D) n hf x
  have hbound : ‖iteratedFDeriv ℝ n (f ∘ forcingReadoutLinear b D) x‖ ≤
      saturationDerivativeConstant n * (‖b‖ / D) ^ n := by
    apply hcomp.trans
    rw [forcingReadoutLinear_norm b hD]
    exact mul_le_mul_of_nonneg_right (hscalar _) (by positivity)
  have heq : forcing b D C₀ K = fun y => D • ((f ∘ forcingReadoutLinear b D) y) := by
    funext y
    simp only [forcing, Function.comp_apply, forcingReadoutLinear_apply, smul_eq_mul, f]
  rw [heq, iteratedFDeriv_const_smul_apply' (hf.comp (forcingReadoutLinear b D).contDiff).contDiffAt,
    norm_smul D (iteratedFDeriv ℝ n (f ∘ forcingReadoutLinear b D) x), Real.norm_eq_abs, abs_of_pos hD]
  exact (mul_le_mul_of_nonneg_left hbound hD.le).trans_eq (mul_assoc _ _ _).symm

theorem forcing_second_derivative_bound (b : E) {D K : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    (C₀ : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ 2 (forcing b D C₀ K) x‖ ≤ saturationDerivativeConstant 2 * ‖b‖ ^ 2 / D := by
  apply (forcing_iteratedFDeriv_bound 2 (by norm_num) b hD hK C₀ x).trans_eq
  field_simp
  ring

theorem forcing_third_derivative_bound (b : E) {D K : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    (C₀ : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ 3 (forcing b D C₀ K) x‖ ≤ saturationDerivativeConstant 3 * ‖b‖ ^ 3 / D ^ 2 := by
  apply (forcing_iteratedFDeriv_bound 3 (by norm_num) b hD hK C₀ x).trans_eq
  field_simp
  ring

end RandomizedFO2003.Cascade
