import LowRank.GaussianRadialIntegral
import LowRank.InverseGramMomentReduction

/-! Finite positive and negative moments of actual Gaussian squared lengths. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

def gaussianMomentFormula (m : ℕ) (a : ℝ) : ℝ :=
  (2 : ℝ) ^ a * Real.Gamma ((m : ℝ) / 2 + a) / Real.Gamma ((m : ℝ) / 2)

theorem gaussianMomentFormula_zero {m : ℕ} (hm : 0 < m) :
    gaussianMomentFormula m 0 = 1 := by
  simp [gaussianMomentFormula, (Real.Gamma_pos_of_pos
    (show 0 < (m : ℝ) / 2 by positivity)).ne']

theorem gaussianMomentFormula_step (m : ℕ) {a : ℝ} (ha : 0 < (m : ℝ) / 2 + a) :
    gaussianMomentFormula m (a + 1) = ((m : ℝ) + 2 * a) * gaussianMomentFormula m a := by
  unfold gaussianMomentFormula
  rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0), ← add_assoc,
    Real.Gamma_add_one ha.ne']
  ring

theorem gaussianMomentFormula_nat {m : ℕ} (hm : 0 < m) (q : ℕ) :
    gaussianMomentFormula m q = ∏ j ∈ Finset.range q, ((m : ℝ) + 2 * j) := by
  induction q with
  | zero => simpa using gaussianMomentFormula_zero hm
  | succ q ih =>
    rw [Nat.cast_succ, gaussianMomentFormula_step m (by positivity), ih,
      Finset.prod_range_succ]
    ring

theorem gaussianMomentFormula_neg_nat {m q : ℕ} (hq : 2 * q < m) :
    gaussianMomentFormula m (-(q : ℝ)) =
      (∏ j ∈ Finset.range q, ((m : ℝ) - 2 * (j + 1)))⁻¹ := by
  induction q with
  | zero => simpa using gaussianMomentFormula_zero (by omega : 0 < m)
  | succ q ih =>
    have hpos : 0 < (m : ℝ) - 2 * (q + 1) := by
      have h : 2 * ((q : ℝ) + 1) < m := by exact_mod_cast hq
      linarith
    have hr := gaussianMomentFormula_step m (a := -((q : ℝ) + 1)) (by linarith)
    have harg : -((q : ℝ) + 1) + 1 = -(q : ℝ) := by ring
    rw [harg, ih (by omega)] at hr
    rw [Nat.cast_succ, Finset.prod_range_succ, mul_inv]
    change gaussianMomentFormula m (-((q : ℝ) + 1)) = _ / ((m : ℝ) - 2 * (q + 1))
    apply (eq_div_iff hpos.ne').2
    convert hr.symm using 1 <;> ring

theorem squaredGaussianLaw_rpow_lintegral {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) :
    (∫⁻ t, ENNReal.ofReal (t ^ a) ∂squaredGaussianLaw m 1) =
      ENNReal.ofReal (gaussianMomentFormula m a) := by
  rw [squaredGaussianLaw, lintegral_map (by fun_prop) (measurable_dot_self m)]
  exact gaussian_radial_lintegral hm ha

theorem gaussianRadialMoment_standard {m : ℕ} (hm : 0 < m) (q : ℕ) :
    gaussianRadialMoment m q 1 =
      ENNReal.ofReal (∏ j ∈ Finset.range q, ((m : ℝ) + 2 * j)) := by
  have h := gaussian_radial_lintegral hm (a := (q : ℝ)) (by positivity)
  simp only [Real.rpow_natCast] at h
  rw [gaussianRadialMoment, h]
  simpa only [gaussianMomentFormula, Real.rpow_natCast] using
    congrArg ENNReal.ofReal (gaussianMomentFormula_nat hm q)

theorem reciprocalSquaredGaussianMoment_standard {m q : ℕ} (hq : 2 * q < m) :
    reciprocalSquaredGaussianMoment m q 1 =
      ENNReal.ofReal ((∏ j ∈ Finset.range q, ((m : ℝ) - 2 * (j + 1)))⁻¹) := by
  have ha : 0 < (m : ℝ) / 2 + -(q : ℝ) := by
    have h : 2 * (q : ℝ) < m := by exact_mod_cast hq
    linarith
  have hm : 0 < m := by omega
  rw [reciprocalSquaredGaussianMoment, squaredGaussianLaw,
    lintegral_map (by fun_prop) (measurable_dot_self m)]
  have he (x : Fin m → ℝ) : (x ⬝ᵥ x)⁻¹ ^ q = (x ⬝ᵥ x) ^ (-(q : ℝ)) := by
    have hn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    rw [Real.rpow_neg hn,
      Real.rpow_natCast, inv_pow]
  simp_rw [he]
  rw [gaussian_radial_lintegral hm ha]
  exact congrArg ENNReal.ofReal (gaussianMomentFormula_neg_nat hq)

theorem gaussianRadialMoment_standard_finite {m : ℕ} (hm : 0 < m) (q : ℕ) :
    gaussianRadialMoment m q 1 < ∞ := by
  rw [gaussianRadialMoment_standard hm q]
  exact ENNReal.ofReal_lt_top

theorem reciprocalSquaredGaussianMoment_standard_finite {m q : ℕ} (hq : 2 * q < m) :
    reciprocalSquaredGaussianMoment m q 1 < ∞ := by
  rw [reciprocalSquaredGaussianMoment_standard hq]
  exact ENNReal.ofReal_lt_top

end
end LowRank
