import Nonsmooth.RegularTwoDimensionalNoSpike
import Nonsmooth.DominatedPotentialContinuity

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- The quantitative two-dimensional no-spike bound from explicit local
conditions on weighted integrands. Continuity of posterior derivatives and
marginal curvature is derived, not assumed. -/
theorem dominated_slice_no_spike {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t))
    (C : RegularSliceMomentContinuity V H) (y : ℝ) :
    (y - ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) ^ 2 +
      (potentialExpectation V (fun _ x => x) y - ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) ^ 2 ≤
    72 * (1 + Real.log (1 / min
      (cdf (realDensityLaw (potentialPartition V)) y)
      (1 - cdf (realDensityLaw (potentialPartition V)) y))) :=
  regular_two_dimensional_no_spike_cdf H G (regularFamily_curvature_continuous H C)
    (regularFamily_regression_derivative_continuous H C) y

theorem dominated_conditional_slice_no_spike {V : ℝ → ℝ → ℝ}
    (H : RegularStrongSliceFamily V) (G : RegularStrongSliceFamily (fun t x => V x t))
    (C : RegularSliceMomentContinuity V H) :
    ∀ᵐ y ∂realDensityLaw (potentialPartition V),
      (y - ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) ^ 2 +
        ((∫ x : ℝ, x ∂condDistrib Prod.snd Prod.fst (potentialJointLaw V) y) -
          ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) ^ 2 ≤
      72 * (1 + Real.log (1 / min
        (cdf (realDensityLaw (potentialPartition V)) y)
        (1 - cdf (realDensityLaw (potentialPartition V)) y))) :=
  regular_conditional_slice_no_spike H G (regularFamily_curvature_continuous H C)
    (regularFamily_regression_derivative_continuous H C)

end
end Nonsmooth
