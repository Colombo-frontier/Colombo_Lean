import LowRank.GaussianSquaredMoments

/-! Variance scaling for the Gaussian radial moment formulas. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem gaussian_scaled_dot_self (m : ℕ) (v : NNReal) (x : Fin m → ℝ) :
    (Real.sqrt v • x) ⬝ᵥ (Real.sqrt v • x) = (v : ℝ) * (x ⬝ᵥ x) := by
  rw [smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt v.coe_nonneg]

theorem gaussian_radial_lintegral_scaled (m : ℕ) (v : NNReal) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, f (x ⬝ᵥ x) ∂iidVectorLaw m v) =
      ∫⁻ x, f ((v : ℝ) * (x ⬝ᵥ x)) ∂iidVectorLaw m 1 := by
  have hscale : Measurable (fun x : Fin m → ℝ => Real.sqrt v • x) :=
    measurable_const.smul measurable_id
  rw [iidVectorLaw_as_scaled]
  have hmap := lintegral_map (μ := standardVectorLaw m) (hf.comp (measurable_dot_self m)) hscale
  simp only [Function.comp_def] at hmap
  rw [hmap]
  simp_rw [gaussian_scaled_dot_self]
  rfl

theorem gaussian_radial_lintegral_variance {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) (v : NNReal) :
    (∫⁻ x, ENNReal.ofReal ((x ⬝ᵥ x) ^ a) ∂iidVectorLaw m v) =
      ENNReal.ofReal ((v : ℝ) ^ a * gaussianMomentFormula m a) := by
  rw [gaussian_radial_lintegral_scaled m v (fun t => ENNReal.ofReal (t ^ a)) (by fun_prop)]
  have he (x : Fin m → ℝ) : ENNReal.ofReal (((v : ℝ) * (x ⬝ᵥ x)) ^ a) =
      ENNReal.ofReal ((v : ℝ) ^ a) * ENNReal.ofReal ((x ⬝ᵥ x) ^ a) := by
    have hn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    rw [Real.mul_rpow v.coe_nonneg hn,
      ENNReal.ofReal_mul (Real.rpow_nonneg v.coe_nonneg a)]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop), gaussian_radial_lintegral hm ha,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg v.coe_nonneg a)]
  rfl

theorem squaredGaussianLaw_rpow_lintegral_variance {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) (v : NNReal) :
    (∫⁻ t, ENNReal.ofReal (t ^ a) ∂squaredGaussianLaw m v) =
      ENNReal.ofReal ((v : ℝ) ^ a * gaussianMomentFormula m a) := by
  rw [squaredGaussianLaw, lintegral_map (by fun_prop) (measurable_dot_self m)]
  exact gaussian_radial_lintegral_variance hm ha v

theorem gaussianRadialMoment_formula {m : ℕ} (hm : 0 < m) (q : ℕ) (v : NNReal) :
    gaussianRadialMoment m q v =
      ENNReal.ofReal ((v : ℝ) ^ q * ∏ j ∈ Finset.range q, ((m : ℝ) + 2 * j)) := by
  have h := gaussian_radial_lintegral_variance hm (a := (q : ℝ)) (by positivity) v
  simp only [Real.rpow_natCast, gaussianMomentFormula_nat hm q] at h
  exact h

theorem reciprocalSquaredGaussianMoment_formula {m q : ℕ} (hq : 2 * q < m) (v : NNReal) :
    reciprocalSquaredGaussianMoment m q v =
      ENNReal.ofReal ((v : ℝ)⁻¹ ^ q *
        (∏ j ∈ Finset.range q, ((m : ℝ) - 2 * (j + 1)))⁻¹) := by
  rw [reciprocalSquaredGaussianMoment, squaredGaussianLaw,
    lintegral_map (by fun_prop) (measurable_dot_self m)]
  have he (x : Fin m → ℝ) : (x ⬝ᵥ x)⁻¹ ^ q = (x ⬝ᵥ x) ^ (-(q : ℝ)) := by
    have hn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    rw [Real.rpow_neg hn,
      Real.rpow_natCast, inv_pow]
  simp_rw [he]
  have ha : 0 < (m : ℝ) / 2 + -(q : ℝ) := by
    have h : 2 * (q : ℝ) < m := by exact_mod_cast hq
    linarith
  rw [gaussian_radial_lintegral_variance (by omega : 0 < m) ha v,
    gaussianMomentFormula_neg_nat hq, Real.rpow_neg v.coe_nonneg,
    Real.rpow_natCast, inv_pow]

end
end LowRank
