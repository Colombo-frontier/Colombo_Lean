import GradientHessian.Fold

/-! Dimension-independent first derivative bounds for the localized block.
All derivatives are derivatives of the literal scalar functions, including seams.
-/

noncomputable section

namespace GradientHessian.Localized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def cutoffSlope (w : ℝ) (c u : E) : ℝ :=
  2 * Profiles.step₁ ((‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2)) / (5 * w ^ 2)

theorem cutoff_hasGradientAt (w : ℝ) (c u : E) :
    HasGradientAt (cutoff w c) ((-cutoffSlope w c u) • (u - c)) u := by
  have hs := ((((hasFDerivAt_id u).sub_const c).norm_sq).sub_const (4 * w ^ 2)).mul_const
    ((5 * w ^ 2)⁻¹)
  simp only [← div_eq_mul_inv] at hs
  have h := ((Profiles.step_derivative _).comp_hasFDerivAt u hs).const_sub 1
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext z
  simp [InnerProductSpace.toDual_apply, real_inner_smul_left, cutoffSlope]
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem cutoffSlope_nonneg {w : ℝ} (hw : 0 < w) (c u : E) : 0 ≤ cutoffSlope w c u := by
  have h := (Profiles.derivative_bounds ((‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2))).1
  rw [Profiles.deriv_step] at h
  unfold cutoffSlope
  positivity

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem cutoff_flat_outside {w : ℝ} (hw : 0 < w) (c u : E) (hu : 3 * w ≤ ‖u - c‖) :
    cutoff w c u = 0 ∧ cutoffSlope w c u = 0 := by
  have harg : 1 ≤ (‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2) := by
    rw [le_div_iff₀ (by positivity : 0 < 5 * w ^ 2)]
    nlinarith [norm_nonneg (u - c)]
  have hd := (Profiles.derivatives_flat_outside (Or.inr harg)).1
  rw [Profiles.deriv_step] at hd
  simp [cutoff, cutoffSlope, Profiles.step_ge_one harg, hd]

theorem cutoff_gradient_bound {w : ℝ} (hw : 0 < w) (c u : E) :
    ‖gradient (cutoff w c) u‖ ≤ 3 / w := by
  rw [(cutoff_hasGradientAt w c u).gradient, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (cutoffSlope_nonneg hw c u)]
  by_cases hu : ‖u - c‖ ≤ 3 * w
  · have hb := (Profiles.derivative_bounds ((‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2))).2
    rw [Profiles.deriv_step] at hb
    have ht := norm_nonneg (u - c)
    have hn : 2 * Profiles.step₁ ((‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2)) * ‖u - c‖
        ≤ 15 * w := by
      have hmul := mul_nonneg (by linarith : 0 ≤ 5 - 2 *
        Profiles.step₁ ((‖u - c‖ ^ 2 - 4 * w ^ 2) / (5 * w ^ 2))) ht
      nlinarith
    unfold cutoffSlope
    rw [div_mul_eq_mul_div]
    calc
      _ ≤ 15 * w / (5 * w ^ 2) := div_le_div_of_nonneg_right hn (by positivity)
      _ = 3 / w := by field_simp; ring
  · rw [(cutoff_flat_outside hw c u (le_of_not_ge hu)).2, zero_mul]
    positivity

theorem perturbation_hasGradientAt {R : ℝ} (hR : 0 < R) (w : ℝ) (c u : E) :
    HasGradientAt (perturbation R w c)
      (cutoff w c u • ((16 / w) • (u - c) - gradient (publicPotential R) u) +
        (well R w c u - publicPotential R u) • gradient (cutoff w c) u) u := by
  have hcut := (cutoff_hasGradientAt w c u).differentiableAt.hasGradientAt
  have hpub := (publicPotential_hasGradientAt hR u).differentiableAt.hasGradientAt
  have hdiff := (well_hasGradientAt R w c u).hasFDerivAt.sub hpub.hasFDerivAt
  have h := hcut.hasFDerivAt.mul hdiff
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext z
  simp [InnerProductSpace.toDual_apply, real_inner_smul_left, inner_add_left, inner_sub_left]

/-- A concrete absolute bound for the first derivative of the compact perturbation. -/
theorem perturbation_gradient_bound {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E) :
    ‖gradient (perturbation R w c) u‖ ≤ 688 := by
  rw [(perturbation_hasGradientAt hR w c u).gradient]
  by_cases hu : ‖u - c‖ ≤ 3 * w
  · have hcut := cutoff_bounds w c u
    have hcutnorm : ‖cutoff w c u‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hcut.1]
      exact hcut.2
    have hwell := well_difference_bounds hR hw c u hu
    have hwellnorm : ‖well R w c u - publicPotential R u‖ ≤ 208 * w := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hwell.1, hwell.2]
    have hlinear : ‖(16 / w) • (u - c)‖ ≤ 48 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 16 / w),
        div_mul_eq_mul_div, div_le_iff₀ hw]
      nlinarith
    have hdiff : ‖(16 / w) • (u - c) - gradient (publicPotential R) u‖ ≤ 64 := by
      have ht := norm_sub_le ((16 / w) • (u - c)) (gradient (publicPotential R) u)
      have hp := publicPotential_gradient_norm_lt hR u
      linarith
    have h1 := mul_le_mul hcutnorm hdiff (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := mul_le_mul hwellnorm (cutoff_gradient_bound hw c u) (norm_nonneg _)
      (by positivity : 0 ≤ 208 * w)
    have hc : (208 * w) * (3 / w) = 624 := by field_simp; ring
    have ht := norm_add_le
      (cutoff w c u • ((16 / w) • (u - c) - gradient (publicPotential R) u))
      ((well R w c u - publicPotential R u) • gradient (cutoff w c) u)
    rw [norm_smul, norm_smul] at ht
    rw [hc] at h2
    nlinarith
  · rcases cutoff_flat_outside hw c u (le_of_not_ge hu) with ⟨hc, hs⟩
    rw [hc, (cutoff_hasGradientAt w c u).gradient, hs]
    norm_num

theorem incoming_hasGradientAt {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E) :
    HasGradientAt (incoming R w c)
      (gradient (publicPotential R) u + gradient (perturbation R w c) u -
        gradient (drive w c) u) u := by
  have hp := (publicPotential_hasGradientAt hR u).differentiableAt.hasGradientAt.hasFDerivAt
  have hψ := (perturbation_hasGradientAt hR w c u).differentiableAt.hasGradientAt.hasFDerivAt
  have hg := (drive_hasGradientAt hw c u).differentiableAt.hasGradientAt.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [incoming, potential, map_add, map_sub] using ((hp.add hψ).sub hg).add_const (512 * R)

theorem incoming_gradient_bound {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E) :
    ‖gradient (incoming R w c) u‖ ≤ 720 := by
  rw [(incoming_hasGradientAt hR hw c u).gradient]
  have h1 := norm_sub_le (gradient (publicPotential R) u + gradient (perturbation R w c) u)
    (gradient (drive w c) u)
  have h2 := norm_add_le (gradient (publicPotential R) u) (gradient (perturbation R w c) u)
  have hp := publicPotential_gradient_norm_lt hR u
  have hψ := perturbation_gradient_bound hR hw c u
  have hg := drive_gradient_norm_lt hw c u
  linarith

theorem port_gradient_bound {w : ℝ} (hw : 0 < w) (c u : E) :
    ‖gradient (port w c) u‖ ≤ 4 / w := by
  rw [(port_hasGradientAt w c u).gradient, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (portSlope_nonneg hw c u)]
  by_cases hu : ‖u - c‖ ≤ 2 * w
  · have hb := (Profiles.derivative_bounds ((‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2))).2
    rw [Profiles.deriv_step] at hb
    have ht := norm_nonneg (u - c)
    have hn : 2 * Profiles.step₁ ((‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2)) * ‖u - c‖
        ≤ 12 * w := by
      have hmul := mul_nonneg (by linarith : 0 ≤ 5 - 2 *
        Profiles.step₁ ((‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2))) ht
      nlinarith
    unfold portSlope
    rw [div_mul_eq_mul_div]
    calc
      _ ≤ 12 * w / (3 * w ^ 2) := div_le_div_of_nonneg_right hn (by positivity)
      _ = 4 / w := by field_simp; ring
  · have harg : 1 ≤ (‖u - c‖ ^ 2 - w ^ 2) / (3 * w ^ 2) := by
      rw [le_div_iff₀ (by positivity : 0 < 3 * w ^ 2)]
      nlinarith [norm_nonneg (u - c), le_of_not_ge hu]
    have hd := (Profiles.derivatives_flat_outside (Or.inr harg)).1
    rw [Profiles.deriv_step] at hd
    simp only [portSlope, hd, mul_zero, zero_div, zero_mul]
    positivity

theorem fderiv_norm_eq_gradient_norm (f : E → ℝ) (u : E) :
    ‖fderiv ℝ f u‖ = ‖gradient f u‖ := by
  simp only [gradient, LinearIsometryEquiv.norm_map]

theorem perturbation_fderiv_bound {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E) :
    ‖fderiv ℝ (perturbation R w c) u‖ ≤ 688 := by
  rw [fderiv_norm_eq_gradient_norm]
  exact perturbation_gradient_bound hR hw c u

theorem incoming_fderiv_bound {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E) :
    ‖fderiv ℝ (incoming R w c) u‖ ≤ 720 := by
  rw [fderiv_norm_eq_gradient_norm]
  exact incoming_gradient_bound hR hw c u

theorem port_fderiv_bound {w : ℝ} (hw : 0 < w) (c u : E) :
    ‖fderiv ℝ (port w c) u‖ ≤ 4 / w := by
  rw [fderiv_norm_eq_gradient_norm]
  exact port_gradient_bound hw c u

theorem publicPotential_fderiv_bound {R : ℝ} (hR : 0 < R) (u : E) :
    ‖fderiv ℝ (publicPotential R) u‖ ≤ 16 := by
  rw [fderiv_norm_eq_gradient_norm]
  exact (publicPotential_gradient_norm_lt hR u).le

end GradientHessian.Localized
