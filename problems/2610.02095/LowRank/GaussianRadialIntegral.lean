import LowRank.GaussianRadialDensity

/-! Gamma-function evaluation of real powers of the squared Gaussian length. -/

namespace LowRank
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
noncomputable section

def radialGaussianCoefficient (m : ℕ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) ^ m * (m : ℝ) *
    (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)

theorem gaussian_radial_integral_aux {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) :
    (∫ x, (x ⬝ᵥ x) ^ a ∂iidVectorLaw m 1) =
      radialGaussianCoefficient m *
        ((1 / 2 : ℝ) ^ (-((m : ℝ) / 2 + a)) * (1 / 2) *
          Real.Gamma ((m : ℝ) / 2 + a)) := by
  letI : NeZero m := ⟨hm.ne'⟩
  rw [iidVectorLaw_standard_integral_radial m (fun t => t ^ a)]
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (fun r : ℝ => Real.exp (-r ^ 2 / 2) * (r ^ 2) ^ a)]
  simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  have he : (∫ r in Set.Ioi (0 : ℝ), r ^ (m - 1) *
      (Real.exp (-r ^ 2 / 2) * (r ^ 2) ^ a)) =
      ∫ r in Set.Ioi (0 : ℝ), r ^ ((m : ℝ) + 2 * a - 1) *
        Real.exp (-(1 / 2 : ℝ) * r ^ (2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hpow : r ^ (m - 1) * (r ^ 2) ^ a = r ^ ((m : ℝ) + 2 * a - 1) := by
      rw [← Real.rpow_natCast_mul hr.le 2 a, ← Real.rpow_natCast,
        ← Real.rpow_add hr, Nat.cast_sub hm, Nat.cast_one]
      congr 1
      ring
    dsimp only
    rw [Real.rpow_two]
    have hex : -(1 / 2 : ℝ) * r ^ 2 = -r ^ 2 / 2 := by ring
    rw [hex, ← hpow]
    ring
  rw [he, integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2)
    (by linarith : -1 < (m : ℝ) + 2 * a - 1) (by norm_num : (0 : ℝ) < 1 / 2)]
  have he1 : -((m : ℝ) + 2 * a - 1 + 1) / 2 = -((m : ℝ) / 2 + a) := by ring
  have he2 : ((m : ℝ) + 2 * a - 1 + 1) / 2 = (m : ℝ) / 2 + a := by ring
  rw [he1, he2]
  simp only [radialGaussianCoefficient]
  ring

theorem radialGaussianCoefficient_normalization {m : ℕ} (hm : 0 < m) :
    radialGaussianCoefficient m *
      ((1 / 2 : ℝ) ^ (-((m : ℝ) / 2)) * (1 / 2) * Real.Gamma ((m : ℝ) / 2)) = 1 := by
  have h := gaussian_radial_integral_aux hm (a := 0) (by positivity)
  simpa only [Real.rpow_zero, integral_const, measureReal_univ_eq_one, smul_eq_mul,
    one_mul, add_zero] using h.symm

theorem gaussian_radial_integral {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) :
    (∫ x, (x ⬝ᵥ x) ^ a ∂iidVectorLaw m 1) =
      (2 : ℝ) ^ a * Real.Gamma ((m : ℝ) / 2 + a) / Real.Gamma ((m : ℝ) / 2) := by
  rw [gaussian_radial_integral_aux hm ha]
  have hn := radialGaussianCoefficient_normalization hm
  have hG : Real.Gamma ((m : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hp : (1 / 2 : ℝ) ^ (-((m : ℝ) / 2 + a)) =
      (1 / 2 : ℝ) ^ (-((m : ℝ) / 2)) * (2 : ℝ) ^ a := by
    rw [neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    congr 1
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [Real.div_rpow zero_le_one (by norm_num), Real.one_rpow, one_div, inv_inv]
  rw [hp]
  apply (eq_div_iff hG).2
  calc
    _ = (radialGaussianCoefficient m *
        ((1 / 2 : ℝ) ^ (-((m : ℝ) / 2)) * (1 / 2) * Real.Gamma ((m : ℝ) / 2))) *
          ((2 : ℝ) ^ a * Real.Gamma ((m : ℝ) / 2 + a)) := by ring
    _ = _ := by rw [hn, one_mul]

theorem gaussian_radial_integrable {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) :
    Integrable (fun x : Fin m → ℝ => (x ⬝ᵥ x) ^ a) (iidVectorLaw m 1) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_radial_integral hm ha]
  exact (div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.Gamma_pos_of_pos ha)) (Real.Gamma_pos_of_pos (by positivity))).ne'

theorem gaussian_radial_lintegral {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 < (m : ℝ) / 2 + a) :
    (∫⁻ x, ENNReal.ofReal ((x ⬝ᵥ x) ^ a) ∂iidVectorLaw m 1) =
      ENNReal.ofReal ((2 : ℝ) ^ a * Real.Gamma ((m : ℝ) / 2 + a) /
        Real.Gamma ((m : ℝ) / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_radial_integrable hm ha)
    (ae_of_all _ (fun x => Real.rpow_nonneg
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))) _)),
    gaussian_radial_integral hm ha]

end
end LowRank
