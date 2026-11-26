import Nonsmooth.WeightedJointDisintegration

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem weighted_joint_disintegration (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (w : β → ℝ) (hw : Measurable w) (hb : ∀ z, w z ≤ 1) :
    (μ.withDensity (fun z => ENNReal.ofReal (w z))).map (fun z => (X z, z)) =
      ((μ.map X).withDensity (kernelWeightMass κ w)) ⊗ₘ weightedPosteriorKernel κ w hw := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpair : Measurable (fun z : β => (X z, z)) := hX.prodMk measurable_id
  have he := map_withDensity_comp μ _ hpair _ (hw.ennreal_ofReal.comp measurable_snd)
  simp only [Function.comp_def] at he
  rw [he, hκ, weightedPosteriorKernel_disintegration _ κ w hw hb]

theorem weighted_observation_density (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (w : β → ℝ) (hw : Measurable w) (hb : ∀ z, w z ≤ 1) :
    (μ.withDensity (fun z => ENNReal.ofReal (w z))).map X =
      (μ.map X).withDensity (kernelWeightMass κ w) := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  letI := weightedPosteriorKernel_markov κ w hw hb
  letI := kernel_weight_density_finite (μ.map X) κ w hb
  have hpair : Measurable (fun z : β => (X z, z)) := hX.prodMk measurable_id
  have he := congrArg (fun ν : Measure (α × β) => ν.map Prod.fst)
    (weighted_joint_disintegration μ X hX κ hκ w hw hb)
  try dsimp only at he
  rw [Measure.map_map measurable_fst hpair, ← Measure.fst, Measure.fst_compProd] at he
  exact he

theorem weighted_law_joint_disintegration (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (w : β → ℝ) (hw : Measurable w) (hb : ∀ z, w z ≤ 1) :
    (weightedDensityLaw μ w).map (fun z => (X z, z)) =
      ((weightedDensityLaw μ w).map X) ⊗ₘ weightedPosteriorKernel κ w hw := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  letI := weightedPosteriorKernel_markov κ w hw hb
  letI := kernel_weight_density_finite (μ.map X) κ w hb
  simp only [weightedDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ, Measure.map_smul]
  rw [weighted_joint_disintegration μ X hX κ hκ w hw hb,
    weighted_observation_density μ X hX κ hκ w hw hb, Measure.compProd_smul_left]

theorem weighted_law_slice_positive (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (w : β → ℝ) (hw : Measurable w) (hb : ∀ z, w z ≤ 1) :
    ∀ᵐ x ∂(weightedDensityLaw μ w).map X, kernelWeightMass κ w x ≠ 0 := by
  have hp : ∀ᵐ x ∂(μ.map X).withDensity (kernelWeightMass κ w), kernelWeightMass κ w x ≠ 0 := by
    rw [ae_withDensity_iff (kernelWeightMass_measurable κ w hw)]
    exact Eventually.of_forall (fun _ hx => hx)
  rw [weightedDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ, Measure.map_smul,
    weighted_observation_density μ X hX κ hκ w hw hb]
  exact Measure.ae_smul_measure hp _

variable [StandardBorelSpace β] [Nonempty β]

/-- Bayes' formula for the actual regular conditional distribution after
bounded reweighting of the prior. -/
theorem weighted_law_posterior (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (w : β → ℝ) (hw : Measurable w) (hb : ∀ z, w z ≤ 1) :
    ∀ᵐ x ∂(weightedDensityLaw μ w).map X,
      condDistrib id X (weightedDensityLaw μ w) x = weightedDensityLaw (κ x) w ∧
        kernelWeightMass κ w x ≠ 0 := by
  letI := weightedPosteriorKernel_markov κ w hw hb
  have he := (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX measurable_id
    (weighted_law_joint_disintegration μ X hX κ hκ w hw hb)).symm
  filter_upwards [he, weighted_law_slice_positive μ X hX κ hκ w hw hb] with x hx hp
  exact ⟨hx.symm.trans (weightedPosteriorKernel_apply κ w hw x hp), hp⟩

end
end Nonsmooth
