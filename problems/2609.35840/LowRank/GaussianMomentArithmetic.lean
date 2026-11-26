import LowRank.GaussianMomentBounds
import Mathlib.Data.Complex.ExponentialBounds

/-! Real-valued bounds for the Gamma ratios used in the Wishart tail estimate. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem gaussianMomentFormula_pos {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) : 0 < gaussianMomentFormula m a := by
  unfold gaussianMomentFormula
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) a) (Real.Gamma_pos_of_pos ha))
    (Real.Gamma_pos_of_pos (by positivity))

theorem gaussianMomentFormula_one {m : ℕ} (hm : 0 < m) :
    gaussianMomentFormula m 1 = m := by
  simpa using gaussianMomentFormula_nat hm 1

theorem gaussianMomentFormula_nat_le {m : ℕ} (hm : 0 < m) (q : ℕ) :
    gaussianMomentFormula m q ≤ ((m : ℝ) + 2 * q) ^ q := by
  have h := gaussianRadialMoment_le hm q 1
  rw [gaussianRadialMoment_standard hm q] at h
  simp only [NNReal.coe_one, one_mul] at h
  rw [← gaussianMomentFormula_nat hm q] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

theorem gaussianMomentFormula_neg_nat_le {m q : ℕ} (hq : 2 * q < m) :
    gaussianMomentFormula m (-(q : ℝ)) ≤ (((m : ℝ) - 2 * q) ^ q)⁻¹ := by
  have h := reciprocalSquaredGaussianMoment_le hq 1
  rw [reciprocalSquaredGaussianMoment_standard hq] at h
  simp only [NNReal.coe_one, inv_one, one_div, inv_pow] at h
  rw [← gaussianMomentFormula_neg_nat hq] at h
  have hp : 0 < (m : ℝ) - 2 * q := by
    have h' : 2 * (q : ℝ) < m := by exact_mod_cast hq
    linarith
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

theorem factorial_ge_pow_div_exp (q : ℕ) :
    ((q : ℝ) / Real.exp 1) ^ q ≤ (q.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (q : ℝ) (Nat.cast_nonneg q) q
  have hf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  rw [div_le_iff₀ hf] at h
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (Real.exp_pos 1) q)).2
  have he : Real.exp (q : ℝ) = Real.exp 1 ^ q := by
    simpa only [mul_one] using Real.exp_nat_mul 1 q
  rw [he] at h
  simpa only [mul_comm] using h

theorem gaussianMomentFormula_one_nat_ge (q : ℕ) :
    ((q : ℝ) / Real.exp 1) ^ q ≤ gaussianMomentFormula 1 q := by
  apply (factorial_ge_pow_div_exp q).trans
  induction q with
  | zero => simp [gaussianMomentFormula_zero (by omega : 0 < 1)]
  | succ q ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
      gaussianMomentFormula_step 1 (by positivity)]
    exact mul_le_mul (by norm_num; linarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]) ih
      (by positivity) (by positivity)

theorem gaussianMomentFormula_half_le_sqrt {m : ℕ} (hm : 0 < m) :
    gaussianMomentFormula m (1 / 2) ≤ Real.sqrt m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hi : Integrable (fun x : Fin m → ℝ => x ⬝ᵥ x) (iidVectorLaw m 1) := by
    simpa only [Real.rpow_one] using gaussian_radial_integrable hm (a := 1) (by positivity)
  have hhalf : Integrable (fun x : Fin m → ℝ => Real.sqrt (x ⬝ᵥ x)) (iidVectorLaw m 1) := by
    simpa only [Real.sqrt_eq_rpow] using
      gaussian_radial_integrable hm (a := 1 / 2) (by positivity)
  have hu := integral_mono hhalf ((hi.add (integrable_const (m : ℝ))).div_const
    (2 * Real.sqrt m)) (fun x => show Real.sqrt (x ⬝ᵥ x) ≤
      (x ⬝ᵥ x + m) / (2 * Real.sqrt m) from by
        apply (le_div_iff₀ (by positivity)).2
        have hx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
        nlinarith [sq_nonneg (Real.sqrt (x ⬝ᵥ x) - Real.sqrt (m : ℝ)),
          Real.sq_sqrt hx, Real.sq_sqrt hmR.le])
  have hfirst : (∫ x, x ⬝ᵥ x ∂iidVectorLaw m 1) = m := by
    have h := gaussian_radial_integral hm (a := 1) (by positivity)
    change (∫ x, (x ⬝ᵥ x) ^ (1 : ℝ) ∂iidVectorLaw m 1) = gaussianMomentFormula m 1 at h
    rw [gaussianMomentFormula_one hm] at h
    simpa only [Real.rpow_one] using h
  have hhalfval : (∫ x, Real.sqrt (x ⬝ᵥ x) ∂iidVectorLaw m 1) =
      gaussianMomentFormula m (1 / 2) := by
    simpa only [Real.sqrt_eq_rpow, gaussianMomentFormula] using
      gaussian_radial_integral hm (a := 1 / 2) (by positivity)
  simp only [Pi.add_apply] at hu
  rw [hhalfval, integral_div, integral_add hi (integrable_const _), hfirst,
    integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hu
  have he : ((m : ℝ) + m) / (2 * Real.sqrt m) = Real.sqrt m := by
    apply (div_eq_iff (by positivity : (2 * Real.sqrt (m : ℝ)) ≠ 0)).2
    nlinarith [Real.sq_sqrt hmR.le]
  rwa [he] at hu

end
end LowRank
