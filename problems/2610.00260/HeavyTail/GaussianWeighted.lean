import HeavyTail.GaussianDirections

/-! Dimension-independent Gaussian exponential weights in two arbitrary directions.
The mixed quadratic bound uses the exact fourth moment and a scaled Young
inequality, giving a direct alternative to Cauchy--Schwarz in `lem:mixed-exp`. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_exp_abs_inner_integrable (b : E) (c : ℝ) :
    Integrable (fun z => Real.exp (c * |⟪b, z⟫_ℝ|)) (euclideanGaussianLaw E) := by
  apply ((gaussian_inner_exp_integrable E b c).add
    (gaussian_inner_exp_integrable E b (-c))).mono'
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_mul_abs_le_two_exps c _

theorem gaussian_exp_abs_inner_bound (b : E) (c : ℝ) :
    (∫ z, Real.exp (c * |⟪b, z⟫_ℝ|) ∂euclideanGaussianLaw E) ≤
      2 * Real.exp (c ^ 2 * ‖b‖ ^ 2 / 2) := by
  have h := integral_mono (gaussian_exp_abs_inner_integrable E b c)
    ((gaussian_inner_exp_integrable E b c).add (gaussian_inner_exp_integrable E b (-c)))
    (fun z => exp_mul_abs_le_two_exps c ⟪b, z⟫_ℝ)
  simp only [Pi.add_apply] at h
  rw [integral_add (gaussian_inner_exp_integrable E b c)
    (gaussian_inner_exp_integrable E b (-c))] at h
  change _ ≤ mgf (fun z => ⟪b, z⟫_ℝ) (euclideanGaussianLaw E) c +
    mgf (fun z => ⟪b, z⟫_ℝ) (euclideanGaussianLaw E) (-c) at h
  rw [gaussian_inner_mgf, gaussian_inner_mgf, neg_sq] at h
  linarith

theorem scaled_young_square {v x y : ℝ} (hv : 0 < v) :
    x * y ^ 2 ≤ (v * x ^ 2 + y ^ 4 / v) / 2 := by
  have he : v * (y ^ 4 / v) = y ^ 4 := mul_div_cancel₀ _ hv.ne'
  have hs := sq_nonneg (v * x - y ^ 2)
  apply (mul_le_mul_left hv).mp
  nlinarith

theorem gaussian_weighted_square_integrable (b u : E) (c : ℝ) :
    Integrable (fun z => Real.exp (c * |⟪b, z⟫_ℝ|) * ⟪u, z⟫_ℝ ^ 2)
      (euclideanGaussianLaw E) := by
  by_cases hu : u = 0
  · simp [hu]
  · have hv : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hdom : Integrable (fun z => (‖u‖ ^ 2 * Real.exp (2 * c * |⟪b, z⟫_ℝ|) +
        ⟪u, z⟫_ℝ ^ 4 / ‖u‖ ^ 2) / 2) (euclideanGaussianLaw E) :=
      (((gaussian_exp_abs_inner_integrable E b (2 * c)).const_mul (‖u‖ ^ 2)).add
        ((gaussian_inner_power_integrable E u 4).div_const (‖u‖ ^ 2))).div_const 2
    apply hdom.mono'
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
        have h := scaled_young_square (x := Real.exp (c * |⟪b, z⟫_ℝ|))
          (y := ⟪u, z⟫_ℝ) hv
        have he : Real.exp (c * |⟪b, z⟫_ℝ|) ^ 2 = Real.exp (2 * c * |⟪b, z⟫_ℝ|) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rwa [he] at h

theorem gaussian_weighted_square_bound (b u : E) (c : ℝ) :
    (∫ z, Real.exp (c * |⟪b, z⟫_ℝ|) * ⟪u, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) ≤
      (Real.exp (2 * c ^ 2 * ‖b‖ ^ 2) + 3 / 2) * ‖u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  · have hv : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hdom : Integrable (fun z => (‖u‖ ^ 2 * Real.exp (2 * c * |⟪b, z⟫_ℝ|) +
        ⟪u, z⟫_ℝ ^ 4 / ‖u‖ ^ 2) / 2) (euclideanGaussianLaw E) :=
      (((gaussian_exp_abs_inner_integrable E b (2 * c)).const_mul (‖u‖ ^ 2)).add
        ((gaussian_inner_power_integrable E u 4).div_const (‖u‖ ^ 2))).div_const 2
    have hpoint (z : E) : Real.exp (c * |⟪b, z⟫_ℝ|) * ⟪u, z⟫_ℝ ^ 2 ≤
        (‖u‖ ^ 2 * Real.exp (2 * c * |⟪b, z⟫_ℝ|) + ⟪u, z⟫_ℝ ^ 4 / ‖u‖ ^ 2) / 2 := by
      have h := scaled_young_square (x := Real.exp (c * |⟪b, z⟫_ℝ|)) (y := ⟪u, z⟫_ℝ) hv
      have he : Real.exp (c * |⟪b, z⟫_ℝ|) ^ 2 = Real.exp (2 * c * |⟪b, z⟫_ℝ|) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rwa [he] at h
    have h := integral_mono (gaussian_weighted_square_integrable E b u c) hdom hpoint
    have heint : (∫ z, (‖u‖ ^ 2 * Real.exp (2 * c * |⟪b, z⟫_ℝ|) +
        ⟪u, z⟫_ℝ ^ 4 / ‖u‖ ^ 2) / 2 ∂euclideanGaussianLaw E) =
        (‖u‖ ^ 2 * (∫ z, Real.exp (2 * c * |⟪b, z⟫_ℝ|) ∂euclideanGaussianLaw E) +
          3 * ‖u‖ ^ 4 / ‖u‖ ^ 2) / 2 := by
      rw [integral_div, integral_add
        ((gaussian_exp_abs_inner_integrable E b (2 * c)).const_mul (‖u‖ ^ 2))
        ((gaussian_inner_power_integrable E u 4).div_const (‖u‖ ^ 2)),
        integral_const_mul, integral_div, gaussian_inner_fourth]
    rw [heint] at h
    have hb := gaussian_exp_abs_inner_bound E b (2 * c)
    have hexp : (2 * c) ^ 2 * ‖b‖ ^ 2 / 2 = 2 * c ^ 2 * ‖b‖ ^ 2 := by ring
    rw [hexp] at hb
    have hq : 3 * ‖u‖ ^ 4 / ‖u‖ ^ 2 = 3 * ‖u‖ ^ 2 := by
      field_simp
      <;> ring
    rw [hq] at h
    have hmul := mul_le_mul_of_nonneg_left hb hv.le
    nlinarith

theorem gaussian_weighted_square_uniform (b u : E) {c : ℝ}
    (hc : c ^ 2 * ‖b‖ ^ 2 ≤ 1) :
    (∫ z, Real.exp (c * |⟪b, z⟫_ℝ|) * ⟪u, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) ≤
      (Real.exp 2 + 3 / 2) * ‖u‖ ^ 2 := by
  apply (gaussian_weighted_square_bound E b u c).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply add_le_add_right
  exact Real.exp_le_exp.mpr (by linarith)

end HeavyTail.GaussianEstimates
