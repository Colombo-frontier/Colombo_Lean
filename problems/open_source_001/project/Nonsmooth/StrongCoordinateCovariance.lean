import Nonsmooth.ParameterizedMarginalCurvature

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem weighted_hessian_determinant_with_margin {a b c ρ θ w : ℝ}
    (hθ : θ < ρ) (hw : 0 ≤ w)
    (h : ∀ p q : ℝ, ρ * (p ^ 2 + w * q ^ 2) ≤
      a * p ^ 2 + 2 * b * p * q + c * q ^ 2) :
    0 < a - θ ∧ b ^ 2 ≤ (a - θ) * (c - θ * w) := by
  have ha : 0 < a - θ := by have h0 := h 1 0; norm_num at h0; linarith
  refine ⟨ha, ?_⟩
  have hpsd (p q : ℝ) : 0 ≤ (a - θ) * p ^ 2 + 2 * b * p * q + (c - θ * w) * q ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hθ.le)
      (add_nonneg (sq_nonneg p) (mul_nonneg hw (sq_nonneg q)))
    nlinarith [h p q]
  have hp : 0 ≤ (a - θ) * ((a - θ) * (c - θ * w) - b ^ 2) := by
    nlinarith [hpsd b (-(a - θ))]
  by_contra hn
  have hh := mul_neg_of_pos_of_neg ha (sub_neg.mpr (lt_of_not_ge hn))
  linarith

/-- Integrating the transverse coordinate preserves the full weighted
Hessian lower bound in every parameter direction. All expectations use
the actual normalized density. -/
theorem strong_coordinate_covariance_curvature
    (U s a f b g : ℝ → ℝ) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w)
    (hs : Continuous s) (ha : Continuous a) (hf : Continuous f) (hb : Continuous b)
    (hdU : ∀ x, HasDerivAt U (s x) x)
    (hds : ∀ x, HasDerivAt s (a x) x)
    (hdf : ∀ x, HasDerivAt f (b x) x)
    (hblock : ∀ x p q, ρ * (p ^ 2 + w * q ^ 2) ≤
      a x * p ^ 2 + 2 * b x * p * q + g x * q ^ 2)
    (hf2 : MemLp f 2 (realDensityLaw (fun x => Real.exp (-U x))))
    (hg : Integrable g (realDensityLaw (fun x => Real.exp (-U x)))) :
    ρ * w ≤ (∫ x, g x ∂realDensityLaw (fun x => Real.exp (-U x))) -
      variance f (realDensityLaw (fun x => Real.exp (-U x))) := by
  let Q := realDensityLaw (fun x => Real.exp (-U x))
  have haρ (x : ℝ) : ρ ≤ a x := by
    have h := hblock x 1 0
    simpa only [one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, mul_one, add_zero] using h
  have hm : Monotone (fun x => s x - ρ * x) :=
    monotone_of_hasDerivAt_nonneg
      (fun x => (hds x).sub ((hasDerivAt_id x).const_mul ρ))
      (fun x => by
        simp only [Pi.zero_apply, mul_one]
        exact sub_nonneg.mpr (haρ x))
  letI : IsProbabilityMeasure Q :=
    (strong_potential_law_probability_and_memLp U s hs hρ hdU hm).1
  have hreserved (θ : ℝ) (hθ0 : 0 < θ) (hθρ : θ < ρ) :
      θ * w ≤ (∫ x, g x ∂Q) - variance f Q := by
    have hdet (x : ℝ) := weighted_hessian_determinant_with_margin hθρ hw (hblock x)
    have hquot (x : ℝ) : (b x) ^ 2 / (a x - θ) ≤ g x - θ * w :=
      (div_le_iff₀ (hdet x).1).mpr (by simpa only [mul_comm] using (hdet x).2)
    have hc : Continuous (fun x => (b x) ^ 2 / (a x - θ)) :=
      (hb.pow 2).div (ha.sub continuous_const) (fun x => (hdet x).1.ne')
    have hgrad : Integrable (fun x => (b x) ^ 2 / (a x - θ)) Q := by
      apply (hg.sub (integrable_const (θ * w))).mono' hc.aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hdet x).1.le)]
        exact hquot x)
    have hBL := full_line_covariance_brascamp_lieb hθ0 U s a f b hs ha hf hb
      hdU hds hdf (fun x => (hdet x).1) hf2 hgrad
    have hI := integral_mono hgrad (hg.sub (integrable_const (θ * w))) hquot
    simp only [Pi.sub_apply] at hI
    rw [integral_sub hg (integrable_const (θ * w)), integral_const,
      probReal_univ, one_smul] at hI
    change variance f Q + θ * (∫ x, x * (f x - ∫ y, f y ∂Q) ∂Q) ^ 2 ≤ _ at hBL
    have hn : 0 ≤ θ * (∫ x, x * (f x - ∫ y, f y ∂Q) ∂Q) ^ 2 := by positivity
    linarith
  let c := (∫ x, g x ∂Q) - variance f Q
  change ρ * w ≤ c
  by_cases hw0 : w = 0
  · have h := hreserved (ρ / 2) (by linarith) (by linarith)
    simpa only [hw0, mul_zero] using h
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  by_contra hn
  have hlt : c / w < ρ := (div_lt_iff₀ hwpos).mpr (lt_of_not_ge hn)
  obtain ⟨θ, hθlow, hθhigh⟩ := exists_between (max_lt hρ hlt)
  have hθ0 : 0 < θ := lt_of_le_of_lt (le_max_left _ _) hθlow
  have hcθ : c < θ * w := (div_lt_iff₀ hwpos).mp
    (lt_of_le_of_lt (le_max_right _ _) hθlow)
  have hh := hreserved θ hθ0 hθhigh
  change θ * w ≤ c at hh
  linarith

end
end Nonsmooth
