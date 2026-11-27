import Nonsmooth.RegularSliceCurvature
import Nonsmooth.PotentialJointDensity

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Explicit analytic hypotheses for a regular two-dimensional potential.
No marginal convexity, normalization, derivative formula, or posterior identity
is a field: these are consequences proved below and in subsequent modules. -/
structure RegularStrongSliceFamily (V : ℝ → ℝ → ℝ) where
  dx : ℝ → ℝ → ℝ
  dxx : ℝ → ℝ → ℝ
  score : ℝ → ℝ → ℝ
  mixed : ℝ → ℝ → ℝ
  gamma : ℝ → ℝ → ℝ
  measurable : Measurable (Function.uncurry V)
  dx_continuous : ∀ t, Continuous (dx t)
  dxx_continuous : ∀ t, Continuous (dxx t)
  score_continuous : ∀ t, Continuous (score t)
  mixed_continuous : ∀ t, Continuous (mixed t)
  dx_derivative : ∀ t x, HasDerivAt (V t) (dx t x) x
  dxx_derivative : ∀ t x, HasDerivAt (dx t) (dxx t x) x
  mixed_derivative : ∀ t x, HasDerivAt (score t) (mixed t x) x
  transverse : ∀ t x, 0 < dxx t x - 1
  hessian : ∀ t x, (mixed t x) ^ 2 ≤ (dxx t x - 1) * (gamma t x - 1)
  mean_regular : ∀ t, PotentialMomentRegularAt V score (fun _ x => x) (fun _ _ => 0) t
  score_regular : ∀ t, PotentialMomentRegularAt V score score gamma t
  partition_regular : ∀ t, PotentialMomentRegularAt V score (fun _ _ => 1) (fun _ _ => 0) t
  score_memLp : ∀ t, MemLp (score t) 2 (realDensityLaw (fun x => Real.exp (-V t x)))
  gamma_integrable : ∀ t, Integrable (gamma t) (realDensityLaw (fun x => Real.exp (-V t x)))

theorem regularFamily_slice_monotone {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) (t : ℝ) :
    Monotone (fun x => H.dx t x - 1 * x) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun x => (H.dxx_derivative t x).sub ((hasDerivAt_id x).const_mul 1))
  intro x
  simpa only [mul_one, Pi.zero_apply] using (H.transverse t x).le

theorem regularFamily_slice_integrable {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) (t : ℝ) :
    Integrable (fun x => Real.exp (-V t x)) := by
  have hc : Continuous (V t) := continuous_iff_continuousAt.mpr
    (fun x => (H.dx_derivative t x).continuousAt)
  simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable
    (V t) (H.dx t) hc (H.dx_continuous t) (by norm_num : (0 : ℝ) < 1)
    (H.dx_derivative t) (regularFamily_slice_monotone H t) 0

theorem regularFamily_slice_probability_and_memLp {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (t : ℝ) :
    IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-V t x))) ∧
      MemLp (fun x : ℝ => x) 2 (realDensityLaw (fun x => Real.exp (-V t x))) :=
  strong_potential_law_probability_and_memLp (V t) (H.dx t) (H.dx_continuous t)
    (by norm_num : (0 : ℝ) < 1) (H.dx_derivative t) (regularFamily_slice_monotone H t)

theorem regularFamily_slice_measurable {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) (t : ℝ) :
    Measurable (V t) :=
  (continuous_iff_continuousAt.mpr (fun x => (H.dx_derivative t x).continuousAt)).measurable

theorem regularFamily_marginal_derivative {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (t : ℝ) :
    HasDerivAt (fun r => -Real.log (potentialPartition V r)) (potentialExpectation V H.score t) t :=
  potentialNegativeLogPartition_derivative V H.score t (regularFamily_slice_measurable H t)
    (regularFamily_slice_integrable H t) (H.partition_regular t)

theorem regularFamily_marginal_score_derivative {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (t : ℝ) :
    HasDerivAt (potentialExpectation V H.score)
      (potentialExpectation V H.gamma t - variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x)))) t :=
  potentialScore_derivative V H.score H.gamma t (regularFamily_slice_measurable H)
    (regularFamily_slice_integrable H) (H.score_regular t) (H.partition_regular t)
    (H.score_memLp t) (H.gamma_integrable t)

theorem regularFamily_marginal_curvature_lower {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (t : ℝ) :
    1 + (deriv (potentialExpectation V (fun _ x => x)) t) ^ 2 ≤
      potentialExpectation V H.gamma t - variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x))) := by
  have hb := regular_slice_regression_curvature V H.dx H.dxx H.score H.mixed H.gamma t
    (regularFamily_slice_measurable H) (regularFamily_slice_integrable H)
    (H.dx_continuous t) (H.dxx_continuous t) (H.score_continuous t) (H.mixed_continuous t)
    (H.dx_derivative t) (H.dxx_derivative t) (H.mixed_derivative t)
    (H.transverse t) (H.hessian t) (H.mean_regular t) (H.score_regular t)
    H.partition_regular (H.score_memLp t) (H.gamma_integrable t)
  have he : deriv (fun r => -Real.log (potentialPartition V r)) = potentialExpectation V H.score := by
    funext r
    exact (regularFamily_marginal_derivative H r).deriv
  rw [he, (regularFamily_marginal_score_derivative H t).deriv] at hb
  exact hb

theorem regularFamily_marginal_strong_score {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) :
    Continuous (potentialExpectation V H.score) ∧
      Monotone (fun t => potentialExpectation V H.score t - 1 * t) := by
  refine ⟨continuous_iff_continuousAt.mpr (fun t => (regularFamily_marginal_score_derivative H t).continuousAt), ?_⟩
  apply monotone_of_hasDerivAt_nonneg
    (fun t => (regularFamily_marginal_score_derivative H t).sub ((hasDerivAt_id t).const_mul 1))
  intro t
  have hb := regularFamily_marginal_curvature_lower H t
  simp only [mul_one, Pi.zero_apply]
  nlinarith [sq_nonneg (deriv (potentialExpectation V (fun _ x => x)) t)]

end
end Nonsmooth
