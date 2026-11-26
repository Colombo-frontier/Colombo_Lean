import Nonsmooth.RegularMarginalConcentration
import Nonsmooth.PotentialJointSwap
import Nonsmooth.KernelExponentialJensen

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem regularFamily_joint_second_integrable {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t)) :
    Integrable (fun p : ℝ × ℝ => p.2) (potentialJointLaw V) := by
  letI := (regularFamily_marginal_probability_and_memLp G).1
  have hi := (regularFamily_marginal_probability_and_memLp G).2.integrable (by norm_num)
  rw [← potentialJointLaw_second_marginal V H.measurable (regularFamily_slice_integrable G)] at hi
  exact (integrable_map_measure measurable_id.aestronglyMeasurable measurable_snd.aemeasurable).mp hi

theorem regularFamily_joint_second_centered_concentration {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t)) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (r * (p.2 - ∫ q : ℝ × ℝ, q.2 ∂potentialJointLaw V)))
      (potentialJointLaw V) ∧
    (∫ p : ℝ × ℝ, Real.exp (r * (p.2 - ∫ q : ℝ × ℝ, q.2 ∂potentialJointLaw V))
      ∂potentialJointLaw V) ≤ Real.exp (r ^ 2 / 2) := by
  have hm : (∫ y : ℝ, y ∂realDensityLaw (potentialPartition (fun t x => V x t))) =
      ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V := by
    rw [← potentialJointLaw_second_marginal V H.measurable (regularFamily_slice_integrable G)]
    exact integral_map_of_stronglyMeasurable measurable_snd measurable_id.stronglyMeasurable
  have hi := regularFamily_marginal_centered_exp_integrable G r
  have hb := regularFamily_marginal_centered_mgf G r
  rw [hm] at hi hb
  have hf : StronglyMeasurable (fun y : ℝ => Real.exp (r * (y - ∫ q : ℝ × ℝ, q.2 ∂potentialJointLaw V))) :=
    (by fun_prop : Continuous (fun y : ℝ => Real.exp (r * (y - ∫ q : ℝ × ℝ, q.2 ∂potentialJointLaw V)))).stronglyMeasurable
  rw [← potentialJointLaw_second_marginal V H.measurable (regularFamily_slice_integrable G)] at hi hb
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mp hi, ?_⟩
  rwa [integral_map_of_stronglyMeasurable measurable_snd hf] at hb

theorem regularFamily_regression_integrable_and_mean {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t)) :
    Integrable (potentialExpectation V (fun _ x => x)) (realDensityLaw (potentialPartition V)) ∧
      (∫ t, potentialExpectation V (fun _ x => x) t ∂realDensityLaw (potentialPartition V)) =
        ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V := by
  letI := (regularFamily_marginal_probability_and_memLp H).1
  letI := potentialSliceKernel_markov V H.measurable (regularFamily_slice_integrable H)
  have hi := regularFamily_joint_second_integrable H G
  rw [potentialJointLaw_disintegrates V H.measurable (regularFamily_slice_integrable H)] at hi ⊢
  exact ⟨kernel_mean_integrable _ _ Prod.snd measurable_snd hi, (Measure.integral_compProd hi).symm⟩

/-- The actual conditional barycenter inherits the second-coordinate centered
MGF, with integrability proved from the actual joint density. -/
theorem regularFamily_regression_centered_concentration {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t)) (r : ℝ) :
    Integrable (fun t => Real.exp (r * (potentialExpectation V (fun _ x => x) t -
      ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V))) (realDensityLaw (potentialPartition V)) ∧
    (∫ t, Real.exp (r * (potentialExpectation V (fun _ x => x) t -
      ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V)) ∂realDensityLaw (potentialPartition V)) ≤ Real.exp (r ^ 2 / 2) := by
  letI := regularFamily_joint_probability H
  letI := (regularFamily_marginal_probability_and_memLp H).1
  letI := potentialSliceKernel_markov V H.measurable (regularFamily_slice_integrable H)
  let m := ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V
  let f : ℝ × ℝ → ℝ := fun p => r * (p.2 - m)
  have hf : Measurable f := by fun_prop
  have hi : Integrable f (potentialJointLaw V) :=
    ((regularFamily_joint_second_integrable H G).sub (integrable_const m)).const_mul r
  have he := regularFamily_joint_second_centered_concentration H G r
  change Integrable (fun p => Real.exp (f p)) (potentialJointLaw V) ∧
    (∫ p, Real.exp (f p) ∂potentialJointLaw V) ≤ Real.exp (r ^ 2 / 2) at he
  rw [potentialJointLaw_disintegrates V H.measurable (regularFamily_slice_integrable H)] at hi he
  have hJ := kernel_exponential_jensen _ _ f hf hi he.1
  have hp (t : ℝ) : (∫ x, f (t, x) ∂potentialSliceKernel V H.measurable t) =
      r * (potentialExpectation V (fun _ x => x) t - m) := by
    letI := (regularFamily_slice_probability_and_memLp H t).1
    have hx := (regularFamily_slice_probability_and_memLp H t).2.integrable (by norm_num)
    change (∫ x, r * (x - m) ∂realDensityLaw (fun x => Real.exp (-V t x))) = _
    rw [integral_const_mul, integral_sub hx (integrable_const m), integral_const,
      measureReal_univ_eq_one, one_smul]
    rfl
  simp_rw [hp] at hJ
  exact ⟨hJ.1, hJ.2.trans he.2⟩

end
end Nonsmooth
