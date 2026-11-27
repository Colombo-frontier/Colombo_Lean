import Nonsmooth.PotentialJointDensity

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem potentialJointMeasure_swap (V : ℝ → ℝ → ℝ) :
    (potentialJointMeasure V).map Prod.swap = potentialJointMeasure (fun t x => V x t) := by
  ext A hA
  rw [Measure.map_apply measurable_swap hA, potentialJointMeasure, potentialJointMeasure,
    withDensity_apply _ (measurable_swap hA), withDensity_apply _ hA,
    ← lintegral_indicator (measurable_swap hA), ← lintegral_indicator hA]
  rw [← lintegral_prod_swap]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ A <;> simp [hp]

theorem potentialJointLaw_swap (V : ℝ → ℝ → ℝ) :
    (potentialJointLaw V).map Prod.swap = potentialJointLaw (fun t x => V x t) := by
  have hm : potentialJointMeasure V univ = potentialJointMeasure (fun t x => V x t) univ := by
    rw [← potentialJointMeasure_swap V, Measure.map_apply measurable_swap MeasurableSet.univ,
      preimage_univ]
  simp only [potentialJointLaw, ProbabilityTheory.cond, Measure.restrict_univ,
    Measure.map_smul, potentialJointMeasure_swap V, hm]

theorem potentialJointLaw_second_marginal (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V))
    (hi : ∀ x, Integrable (fun t => Real.exp (-V t x))) :
    (potentialJointLaw V).map Prod.snd = realDensityLaw (potentialPartition (fun t x => V x t)) := by
  have hs : Measurable (Function.uncurry (fun t x => V x t)) := hV.comp measurable_swap
  have he := potentialJointLaw_marginal (fun t x => V x t) hs hi
  rw [← potentialJointLaw_swap V, Measure.map_map measurable_fst measurable_swap] at he
  exact he

end
end Nonsmooth
