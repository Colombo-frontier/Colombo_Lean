import Nonsmooth.ConditionalJointImage
import Nonsmooth.DominatedSliceNoSpike
import Nonsmooth.RankQuantileMoment

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

/-- A regular two-dimensional image law controls the actual conditional mean
of the original scalar random variable, with its own marginal rank. -/
theorem regular_joint_image_no_spike (μ : Measure α) [IsProbabilityMeasure μ]
    (X Y : α → ℝ) (hX : Measurable X) (hY : Measurable Y)
    {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V)
    (G : RegularStrongSliceFamily (fun t x => V x t)) (C : RegularSliceMomentContinuity V H)
    (hlaw : μ.map (fun a => (X a, Y a)) = potentialJointLaw V) :
    ∀ᵐ y ∂μ.map X,
      (y - ∫ a, X a ∂μ) ^ 2 +
        ((∫ w : ℝ, w ∂condDistrib Y X μ y) - ∫ a, Y a ∂μ) ^ 2 ≤
          72 * (1 + rankQuantileLog (cdf (μ.map X) y)) := by
  have hm : μ.map X = realDensityLaw (potentialPartition V) := by
    rw [← potentialJointLaw_marginal V H.measurable (regularFamily_slice_integrable H), ← hlaw,
      Measure.map_map measurable_fst (hX.prodMk hY)]
    rfl
  have hp : condDistrib Prod.snd Prod.fst (potentialJointLaw V) = condDistrib Y X μ := by
    simp only [← hlaw, condDistrib_joint_image]
  have hmx : (∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) = ∫ a, X a ∂μ := by
    rw [← hm]
    exact integral_map_of_stronglyMeasurable hX stronglyMeasurable_id
  have hmy : (∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) = ∫ a, Y a ∂μ := by
    rw [← hlaw]
    exact integral_map_of_stronglyMeasurable (hX.prodMk hY) measurable_snd.stronglyMeasurable
  have h := dominated_conditional_slice_no_spike H G C
  rw [hmx, hmy, ← hm, hp] at h
  exact h

end
end Nonsmooth
