import Nonsmooth.FullLineCovarianceBrascampLieb

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A positive two-by-two Hessian determinant bounds the score variance plus
the squared coordinate-score covariance under the actual scalar slice law. -/
theorem scalar_slice_score_covariance_bound (U s v f f' γ : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hfd : ∀ x, HasDerivAt f (f' x) x) (hv1 : ∀ x, 0 < v x - 1)
    (hHessian : ∀ x, (f' x) ^ 2 ≤ (v x - 1) * (γ x - 1))
    (hf2 : MemLp f 2 (realDensityLaw (fun x => Real.exp (-U x))))
    (hγ : Integrable γ (realDensityLaw (fun x => Real.exp (-U x)))) :
    let Q := realDensityLaw (fun x => Real.exp (-U x))
    variance f Q + (∫ x, x * (f x - ∫ y, f y ∂Q) ∂Q) ^ 2 ≤ (∫ x, γ x ∂Q) - 1 := by
  dsimp only
  have hmono : Monotone (fun x => s x - 1 * x) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hsd x).sub ((hasDerivAt_id x).const_mul 1))
    intro x
    simpa only [mul_one, Pi.zero_apply] using (hv1 x).le
  letI := (strong_potential_law_probability_and_memLp U s hs (by norm_num : (0 : ℝ) < 1) hd hmono).1
  have hquot (x : ℝ) : (f' x) ^ 2 / (v x - 1) ≤ γ x - 1 :=
    (div_le_iff₀ (hv1 x)).mpr (by simpa only [mul_comm] using hHessian x)
  have hgradc : Continuous (fun x => (f' x) ^ 2 / (v x - 1)) :=
    (hf'.pow 2).div (hv.sub continuous_const) (fun x => (hv1 x).ne')
  have hgrad : Integrable (fun x => (f' x) ^ 2 / (v x - 1))
      (realDensityLaw (fun x => Real.exp (-U x))) := by
    apply (hγ.sub (integrable_const (1 : ℝ))).mono' hgradc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hv1 x).le)]
    exact hquot x
  have hb := full_line_covariance_brascamp_lieb (by norm_num : (0 : ℝ) < 1)
    U s v f f' hs hv hf hf' hd hsd hfd hv1 hf2 hgrad
  try dsimp only at hb
  simp only [one_mul] at hb
  have he := integral_mono hgrad (hγ.sub (integrable_const (1 : ℝ))) hquot
  simp only [Pi.sub_apply] at he
  rw [integral_sub hγ (integrable_const (1 : ℝ)), integral_const,
    measureReal_univ_eq_one, smul_eq_mul, one_mul] at he
  exact hb.trans he

/-- Once the marginal second-derivative and regression derivative identities
are supplied, the Hessian bound gives the curvature control used by no-spike.
Those analytic differentiation identities remain explicit hypotheses here. -/
theorem scalar_slice_regression_curvature (U s v f f' γ : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hfd : ∀ x, HasDerivAt f (f' x) x) (hv1 : ∀ x, 0 < v x - 1)
    (hHessian : ∀ x, (f' x) ^ 2 ≤ (v x - 1) * (γ x - 1))
    (hf2 : MemLp f 2 (realDensityLaw (fun x => Real.exp (-U x))))
    (hγ : Integrable γ (realDensityLaw (fun x => Real.exp (-U x))))
    (m' curvature : ℝ)
    (hm : m' = -(∫ x, x * (f x - ∫ y, f y ∂realDensityLaw (fun y => Real.exp (-U y)))
      ∂realDensityLaw (fun x => Real.exp (-U x))))
    (hcurvature : curvature = (∫ x, γ x ∂realDensityLaw (fun x => Real.exp (-U x))) -
      variance f (realDensityLaw (fun x => Real.exp (-U x)))) :
    1 + m' ^ 2 ≤ curvature := by
  have hb := scalar_slice_score_covariance_bound U s v f f' γ hs hv hf hf' hd hsd hfd hv1 hHessian hf2 hγ
  try dsimp only at hb
  rw [hm, neg_sq, hcurvature]
  linarith

end
end Nonsmooth
