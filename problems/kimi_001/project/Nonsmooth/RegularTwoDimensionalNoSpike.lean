import Nonsmooth.RegressionConcentration
import Nonsmooth.UnitMGFNoSpike

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem regularFamily_regression_hasDerivAt {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (t : ℝ) :
    HasDerivAt (potentialExpectation V (fun _ x => x))
      (deriv (potentialExpectation V (fun _ x => x)) t) t := by
  have hd := potentialRegression_derivative V H.score t (regularFamily_slice_measurable H)
    (regularFamily_slice_integrable H) (H.mean_regular t) (H.partition_regular t)
    (regularFamily_slice_probability_and_memLp H t).2 (H.score_memLp t)
  rwa [hd.deriv]

/-- A two-dimensional no-spike estimate for the actual density and actual slice
barycenter. Both coordinate orientations satisfy explicit regular-family
hypotheses. Continuity of marginal curvature and regression derivative is explicit. -/
theorem regular_two_dimensional_no_spike {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t))
    (hc : Continuous (fun t => potentialExpectation V H.gamma t -
      variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x)))))
    (hr : Continuous (deriv (potentialExpectation V (fun _ x => x)))) (y : ℝ) :
    (y - ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) ^ 2 +
      (potentialExpectation V (fun _ x => x) y - ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) ^ 2 ≤
    72 * (1 + Real.log (1 / min
      ((realDensityLaw (potentialPartition V)).real (Iic y))
      ((realDensityLaw (potentialPartition V)).real (Ioi y)))) := by
  let U : ℝ → ℝ := fun t => -Real.log (potentialPartition V t)
  let s := potentialExpectation V H.score
  let v : ℝ → ℝ := fun t => potentialExpectation V H.gamma t -
    variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x)))
  let m := potentialExpectation V (fun _ x => x)
  let a := ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)
  let b := ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V
  have hden : (fun t => Real.exp (-U t)) = potentialPartition V := regularFamily_marginal_density H
  have hi : Integrable (fun t => Real.exp (-U t)) := by
    rw [hden]
    exact regularFamily_partition_integrable H
  have hs : Continuous s := (regularFamily_marginal_strong_score H).1
  have hd : ∀ t, HasDerivAt U (s t) t := regularFamily_marginal_derivative H
  have hsd : ∀ t, HasDerivAt s (v t) t := regularFamily_marginal_score_derivative H
  have hb (t : ℝ) : 1 + (deriv m t) ^ 2 ≤ v t := regularFamily_marginal_curvature_lower H t
  have hcoord : (y - a) ^ 2 ≤ 36 * (1 + Real.log (1 /
      min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
        ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y)))) := by
    apply unit_mgf_no_spike_quantile U s v (fun t => t - a) (fun _ => 1)
      hs hc continuous_const hd hsd (fun t => (hasDerivAt_id t).sub_const a) _ hi _ _ y
    · intro t
      nlinarith [hb t, sq_nonneg (deriv m t)]
    · intro r
      rw [hden]
      exact regularFamily_marginal_centered_exp_integrable H r
    · intro r
      rw [hden]
      exact regularFamily_marginal_centered_mgf H r
  have hreg : (m y - b) ^ 2 ≤ 36 * (1 + Real.log (1 /
      min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
        ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y)))) := by
    apply unit_mgf_no_spike_quantile U s v (fun t => m t - b) (deriv m)
      hs hc hr hd hsd (fun t => (regularFamily_regression_hasDerivAt H t).sub_const b) _ hi _ _ y
    · intro t
      linarith [hb t]
    · intro r
      rw [hden]
      exact (regularFamily_regression_centered_concentration H G r).1
    · intro r
      rw [hden]
      exact (regularFamily_regression_centered_concentration H G r).2
  rw [hden] at hcoord hreg
  change (y - a) ^ 2 + (m y - b) ^ 2 ≤ _
  linarith

theorem regular_two_dimensional_no_spike_cdf {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t))
    (hc : Continuous (fun t => potentialExpectation V H.gamma t -
      variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x)))))
    (hr : Continuous (deriv (potentialExpectation V (fun _ x => x)))) (y : ℝ) :
    (y - ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) ^ 2 +
      (potentialExpectation V (fun _ x => x) y - ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) ^ 2 ≤
    72 * (1 + Real.log (1 / min
      (cdf (realDensityLaw (potentialPartition V)) y)
      (1 - cdf (realDensityLaw (potentialPartition V)) y))) := by
  letI := (regularFamily_marginal_probability_and_memLp H).1
  have hright : (realDensityLaw (potentialPartition V)).real (Ioi y) =
      1 - cdf (realDensityLaw (potentialPartition V)) y := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]
  simpa only [hright, cdf_eq_real] using regular_two_dimensional_no_spike H G hc hr y

/-- The same estimate for the actual regular conditional distribution, rather
than only for an abstract family of slice laws. -/
theorem regular_conditional_slice_no_spike {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t))
    (hc : Continuous (fun t => potentialExpectation V H.gamma t -
      variance (H.score t) (realDensityLaw (fun x => Real.exp (-V t x)))))
    (hr : Continuous (deriv (potentialExpectation V (fun _ x => x)))) :
    ∀ᵐ y ∂realDensityLaw (potentialPartition V),
      (y - ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) ^ 2 +
        ((∫ x : ℝ, x ∂condDistrib Prod.snd Prod.fst (potentialJointLaw V) y) -
          ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) ^ 2 ≤
      72 * (1 + Real.log (1 / min
        (cdf (realDensityLaw (potentialPartition V)) y)
        (1 - cdf (realDensityLaw (potentialPartition V)) y))) := by
  filter_upwards [potentialJointLaw_posterior V H.measurable (regularFamily_slice_integrable H)] with y hy
  rw [hy]
  exact regular_two_dimensional_no_spike_cdf H G hc hr y

end
end Nonsmooth
