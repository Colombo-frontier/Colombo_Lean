import GaussianIntegral254

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Paper254

theorem gaussian_centered_integrable (u m : ℝ) (q : ℝ≥0) :
    Integrable (fun x => (x-m)^2) (gaussianReal u q) := by
  have h : MemLp (fun x : ℝ => x-m) 2 (gaussianReal u q) :=
    (memLp_id_gaussianReal 2).sub (memLp_const m)
  exact h.integrable_sq

theorem gaussian_centered_second_moment (u m : ℝ) (q : ℝ≥0) :
    (∫ x,(x-m)^2 ∂gaussianReal u q)=(q:ℝ)+(u-m)^2 := by
  have hv := variance_fun_id_gaussianReal (μ := u) (v := q)
  rw [variance_eq_integral measurable_id'.aemeasurable,integral_id_gaussianReal] at hv
  have hi : Integrable (fun x : ℝ => x) (gaussianReal u q) :=
    (memLp_id_gaussianReal 2).integrable (by norm_num)
  have hcenter : Integrable (fun x : ℝ => x-u) (gaussianReal u q) := hi.sub (integrable_const u)
  have he : ∀ x : ℝ,(x-m)^2=(x-u)^2+2*(u-m)*(x-u)+(u-m)^2 := by intro x; ring
  rw [show (fun x : ℝ => (x-m)^2)=(fun x => (x-u)^2+2*(u-m)*(x-u)+(u-m)^2) from funext he]
  have h1 : Integrable (fun x => (x-u)^2+2*(u-m)*(x-u)) (gaussianReal u q) :=
    (gaussian_centered_integrable u u q).add (hcenter.const_mul (2*(u-m)))
  rw [integral_add h1 (integrable_const ((u-m)^2)),
    integral_add (gaussian_centered_integrable u u q) (hcenter.const_mul (2*(u-m))),integral_const_mul,
    integral_sub hi (integrable_const u)]
  simp [hv,integral_id_gaussianReal]

theorem gaussian_log_density (u x : ℝ) (q : ℝ≥0) (hq : q ≠ 0) :
    Real.log (gaussianPDFReal u q x)= -Real.log (2*Real.pi*(q:ℝ))/2-(x-u)^2/(2*(q:ℝ)) := by
  have hp : (0:ℝ)<q := by exact_mod_cast (pos_iff_ne_zero.mpr hq)
  rw [gaussianPDFReal_def,Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_inv,Real.log_sqrt (by positivity),Real.log_exp]
  ring

theorem gaussian_log_density_ratio (u m x : ℝ) (q c : ℝ≥0) (hq : q ≠ 0) (hc : c ≠ 0) :
    Real.log (gaussianPDFReal u q x/gaussianPDFReal m c x)=
      Real.log ((c:ℝ)/(q:ℝ))/2+((x-m)^2/(c:ℝ)-(x-u)^2/(q:ℝ))/2 := by
  have hqp : (0:ℝ)<q := by exact_mod_cast (pos_iff_ne_zero.mpr hq)
  have hcp : (0:ℝ)<c := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
  rw [Real.log_div (gaussianPDFReal_pos u q x hq).ne' (gaussianPDFReal_pos m c x hc).ne',
    gaussian_log_density u x q hq,gaussian_log_density m x c hc,
    Real.log_mul (by positivity : (2:ℝ)*Real.pi ≠ 0) hqp.ne',
    Real.log_mul (by positivity : (2:ℝ)*Real.pi ≠ 0) hcp.ne',Real.log_div hcp.ne' hqp.ne']
  ring

/-- The coordinate potential equals the integral of the actual log density
ratio. This theorem is about probability densities, not a renamed formula. -/
theorem gaussian_density_entropy (u m : ℝ) (q c : ℝ≥0) (hq : q ≠ 0) (hc : c ≠ 0) :
    (∫ x,Real.log (gaussianPDFReal u q x/gaussianPDFReal m c x) ∂gaussianReal u q)=
      coordinateKL q c (u-m) := by
  simp_rw [gaussian_log_density_ratio u m _ q c hq hc]
  have hint : Integrable (fun x => ((x-m)^2/(c:ℝ)-(x-u)^2/(q:ℝ))/2) (gaussianReal u q) :=
    (((gaussian_centered_integrable u m q).div_const _).sub
      ((gaussian_centered_integrable u u q).div_const _)).div_const 2
  rw [integral_add (integrable_const _) hint]
  simp only [integral_div]
  rw [integral_sub ((gaussian_centered_integrable u m q).div_const (c:ℝ))
      ((gaussian_centered_integrable u u q).div_const (q:ℝ)),integral_div,integral_div,
    gaussian_centered_second_moment,gaussian_centered_second_moment]
  have hqp : (q:ℝ) ≠ 0 := by exact_mod_cast hq
  simp [coordinateKL,covariancePenalty,hqp]
  ring

end Paper254
#print axioms Paper254.gaussian_density_entropy
