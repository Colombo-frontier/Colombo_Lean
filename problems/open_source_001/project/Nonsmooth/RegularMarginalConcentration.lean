import Nonsmooth.RegularStrongSliceFamily
import Nonsmooth.StrongPotentialMGF

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem regularFamily_marginal_density {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) :
    (fun t => Real.exp (-(-Real.log (potentialPartition V t)))) = potentialPartition V := by
  funext t
  simpa only [neg_neg, potentialPartition] using Real.exp_log (integral_exp_pos (regularFamily_slice_integrable H t))

/-- The marginal density is integrable as a consequence of its proved curvature;
joint normalization is not an additional assumption. -/
theorem regularFamily_partition_integrable {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) :
    Integrable (potentialPartition V) := by
  have hs := regularFamily_marginal_strong_score H
  have hU : Continuous (fun t => -Real.log (potentialPartition V t)) :=
    continuous_iff_continuousAt.mpr (fun t => (regularFamily_marginal_derivative H t).continuousAt)
  have hi := strong_potential_polynomial_integrable _ _ hU hs.1 (by norm_num : (0 : ℝ) < 1)
    (regularFamily_marginal_derivative H) hs.2 0
  simp only [pow_zero, one_mul] at hi
  rwa [regularFamily_marginal_density H] at hi

theorem regularFamily_joint_integrable {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-V p.1 p.2)) ((volume : Measure ℝ).prod volume) := by
  have hw : Measurable (fun p : ℝ × ℝ => Real.exp (-V p.1 p.2)) :=
    Real.continuous_exp.measurable.comp H.measurable.neg
  apply (integrable_prod_iff hw.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (regularFamily_slice_integrable H), ?_⟩
  convert! regularFamily_partition_integrable H using 1 <;>
    simp only [potentialPartition, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] <;> rfl

theorem regularFamily_joint_probability {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) :
    IsProbabilityMeasure (potentialJointLaw V) :=
  potentialJointLaw_probability V (regularFamily_joint_integrable H)

theorem regularFamily_marginal_probability_and_memLp {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) :
    IsProbabilityMeasure (realDensityLaw (potentialPartition V)) ∧
      MemLp (fun t : ℝ => t) 2 (realDensityLaw (potentialPartition V)) := by
  have hs := regularFamily_marginal_strong_score H
  have hb := strong_potential_law_probability_and_memLp _ _ hs.1 (by norm_num : (0 : ℝ) < 1)
    (regularFamily_marginal_derivative H) hs.2
  rwa [regularFamily_marginal_density H] at hb

theorem regularFamily_marginal_variance {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V) :
    variance (fun t : ℝ => t) (realDensityLaw (potentialPartition V)) ≤ 1 := by
  have hs := regularFamily_marginal_strong_score H
  have hb := strong_potential_law_variance _ _ hs.1 (by norm_num : (0 : ℝ) < 1)
    (regularFamily_marginal_derivative H) hs.2
  simpa only [regularFamily_marginal_density H, inv_one] using hb

theorem regularFamily_marginal_centered_exp_integrable {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (r : ℝ) :
    Integrable (fun t => Real.exp (r * (t - ∫ y : ℝ, y ∂realDensityLaw (potentialPartition V))))
      (realDensityLaw (potentialPartition V)) := by
  have hs := regularFamily_marginal_strong_score H
  have hb := strong_potential_centered_exp_integrable _ _ hs.1 (by norm_num : (0 : ℝ) < 1)
    (regularFamily_marginal_derivative H) hs.2 r
  simpa only [regularFamily_marginal_density H] using hb

/-- Sharp centered MGF for the actual first marginal of the two-dimensional law. -/
theorem regularFamily_marginal_centered_mgf {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (r : ℝ) :
    (∫ t, Real.exp (r * (t - ∫ y : ℝ, y ∂realDensityLaw (potentialPartition V)))
      ∂realDensityLaw (potentialPartition V)) ≤ Real.exp (r ^ 2 / 2) := by
  have hs := regularFamily_marginal_strong_score H
  have hb := strong_potential_centered_mgf _ _ hs.1 (by norm_num : (0 : ℝ) < 1)
    (regularFamily_marginal_derivative H) hs.2 r
  simpa only [regularFamily_marginal_density H, mul_one] using hb

end
end Nonsmooth
