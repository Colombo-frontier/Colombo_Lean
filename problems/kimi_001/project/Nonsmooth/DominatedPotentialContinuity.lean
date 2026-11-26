import Nonsmooth.RegularStrongSliceFamily

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- Local domination and pointwise continuity of the actual weighted integrand,
before normalization. This does not assume continuity of an integral or posterior. -/
def PotentialMomentContinuousAt (V F : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ B : ℝ → ℝ, Integrable B ∧
    (∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun x => F r x * Real.exp (-V r x))) ∧
    (∀ᶠ r in 𝓝 t, ∀ᵐ x ∂(volume : Measure ℝ), ‖F r x * Real.exp (-V r x)‖ ≤ B x) ∧
    ∀ᵐ x ∂(volume : Measure ℝ), ContinuousAt (fun r => F r x * Real.exp (-V r x)) t

theorem potentialWeightedIntegral_continuousAt (V F : ℝ → ℝ → ℝ) (t : ℝ)
    (h : PotentialMomentContinuousAt V F t) : ContinuousAt (potentialWeightedIntegral V F) t := by
  obtain ⟨B, hB, hm, hb, hc⟩ := h
  exact continuousAt_of_dominated hm hb hB hc

theorem regularFamily_expectation_continuous {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, PotentialMomentContinuousAt V F t) : Continuous (potentialExpectation V F) := by
  have he : potentialExpectation V F = fun t => potentialWeightedIntegral V F t / potentialPartition V t := by
    funext t
    exact potentialExpectation_eq_ratio V F t (regularFamily_slice_measurable H t) (regularFamily_slice_integrable H t)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (potentialWeightedIntegral_continuousAt V F t (hF t)).div
    (potentialPartition_derivative V H.score t (H.partition_regular t)).continuousAt
    (integral_exp_pos (regularFamily_slice_integrable H t)).ne'

/-- Only the three additional weighted moments needed for continuity of the
marginal curvature and of the regression derivative are requested. -/
structure RegularSliceMomentContinuity (V : ℝ → ℝ → ℝ) (H : RegularStrongSliceFamily V) : Prop where
  gamma : ∀ t, PotentialMomentContinuousAt V H.gamma t
  square : ∀ t, PotentialMomentContinuousAt V (fun r x => (H.score r x) ^ 2) t
  cross : ∀ t, PotentialMomentContinuousAt V (fun r x => x * H.score r x) t

theorem regularFamily_curvature_continuous {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (C : RegularSliceMomentContinuity V H) :
    Continuous (fun t => potentialExpectation V H.gamma t -
      variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x)))) := by
  have he : (fun t => variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x)))) =
      fun t => potentialExpectation V (fun r x => (H.score r x) ^ 2) t - (potentialExpectation V H.score t) ^ 2 := by
    funext t
    letI := (regularFamily_slice_probability_and_memLp H t).1
    simpa only [potentialExpectation, Pi.pow_apply] using variance_eq_sub (H.score_memLp t)
  simp_rw [show ∀ t, variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x))) =
    potentialExpectation V (fun r x => (H.score r x) ^ 2) t - (potentialExpectation V H.score t) ^ 2
      from congrFun he]
  exact (regularFamily_expectation_continuous H H.gamma C.gamma).sub
    ((regularFamily_expectation_continuous H _ C.square).sub ((regularFamily_marginal_strong_score H).1.pow 2))

theorem regularFamily_regression_derivative_continuous {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (C : RegularSliceMomentContinuity V H) :
    Continuous (deriv (potentialExpectation V (fun _ x => x))) := by
  have hm (t : ℝ) := potentialRegression_derivative V H.score t (regularFamily_slice_measurable H)
    (regularFamily_slice_integrable H) (H.mean_regular t) (H.partition_regular t)
    (regularFamily_slice_probability_and_memLp H t).2 (H.score_memLp t)
  have hmc : Continuous (potentialExpectation V (fun _ x => x)) :=
    continuous_iff_continuousAt.mpr (fun t => (hm t).continuousAt)
  have he : deriv (potentialExpectation V (fun _ x => x)) = fun t =>
      -(potentialExpectation V (fun r x => x * H.score r x) t -
        potentialExpectation V (fun _ x => x) t * potentialExpectation V H.score t) := by
    funext t
    rw [(hm t).deriv]
    letI := (regularFamily_slice_probability_and_memLp H t).1
    have hx := (regularFamily_slice_probability_and_memLp H t).2
    rw [integral_mul_centered_eq _ (H.score t) (fun x : ℝ => x)
      (hx.integrable (by norm_num)) (hx.integrable_mul (H.score_memLp t))]
    rfl
  rw [he]
  exact ((regularFamily_expectation_continuous H _ C.cross).sub
    (hmc.mul (regularFamily_marginal_strong_score H).1)).neg

end
end Nonsmooth
