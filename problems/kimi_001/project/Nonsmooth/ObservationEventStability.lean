import Nonsmooth.GaussianSlabCovariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {β : Type} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]

theorem condDistrib_real_fiber (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → ℝ) (hX : Measurable X) :
    ∀ᵐ x ∂μ.map X, ∀ᵐ z ∂condDistrib id X μ x, X z = x := by
  have hg : MeasurableSet {p : ℝ × β | X p.2 = p.1} :=
    (hX.comp measurable_snd).stronglyMeasurable.measurableSet_eq_fun measurable_fst.stronglyMeasurable
  have hj : ∀ᵐ p ∂μ.map (fun z => (X z, z)), X p.2 = p.1 :=
    (ae_map_iff (hX.prodMk measurable_id).aemeasurable hg).mpr (Eventually.of_forall (fun _ => rfl))
  have he : (μ.map X) ⊗ₘ condDistrib id X μ = μ.map (fun z => (X z, z)) :=
    compProd_map_condDistrib aemeasurable_id
  rw [← he] at hj
  exact (Measure.ae_compProd_iff hg).mp hj

omit [StandardBorelSpace β] [Nonempty β] in
theorem cond_eq_self_of_ae_mem (μ : Measure β) [IsProbabilityMeasure μ]
    {A : Set β} (hA : MeasurableSet A) (hmem : ∀ᵐ z ∂μ, z ∈ A) : μ[|A] = μ := by
  have hm : μ A = 1 := (mem_ae_iff_prob_eq_one hA).mp hmem
  rw [ProbabilityTheory.cond, hm, inv_one, one_smul, Measure.restrict_eq_self_of_ae_mem hmem]

/-- Restricting an observation to a measurable event leaves its regular
conditional law unchanged at almost every retained observation. -/
theorem condDistrib_condition_observation (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → ℝ) (hX : Measurable X) (D : Set ℝ) (hD : MeasurableSet D) :
    ∀ᵐ x ∂(μ[|X ⁻¹' D]).map X,
      condDistrib id X (μ[|X ⁻¹' D]) x = condDistrib id X μ x := by
  have he := event_conditioned_posterior μ X hX (condDistrib id X μ)
    (compProd_map_condDistrib aemeasurable_id).symm (X ⁻¹' D) (hX hD)
  have hf : ∀ᵐ x ∂(μ[|X ⁻¹' D]).map X,
      ∀ᵐ z ∂condDistrib id X μ x, X z = x := by
    rw [← conditioning_map_preimage μ X hX D hD]
    exact cond_absolutelyContinuous.ae_le (condDistrib_real_fiber μ X hX)
  have hd : ∀ᵐ x ∂(μ[|X ⁻¹' D]).map X, x ∈ D := by
    rw [← conditioning_map_preimage μ X hX D hD]
    exact ae_cond_mem hD
  filter_upwards [he, hf, hd] with x hx hf hd
  rw [hx.1]
  apply cond_eq_self_of_ae_mem _ (hX hD)
  filter_upwards [hf] with z hz
  change X z ∈ D
  rw [hz]
  exact hd

theorem condDistrib_property_condition_observation (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → ℝ) (hX : Measurable X) (D : Set ℝ) (hD : MeasurableSet D)
    (P : Measure β → Prop) (hP : ∀ᵐ x ∂μ.map X, P (condDistrib id X μ x)) :
    ∀ᵐ x ∂(μ[|X ⁻¹' D]).map X, P (condDistrib id X (μ[|X ⁻¹' D]) x) := by
  have hp : ∀ᵐ x ∂(μ[|X ⁻¹' D]).map X, P (condDistrib id X μ x) := by
    rw [← conditioning_map_preimage μ X hX D hD]
    exact cond_absolutelyContinuous.ae_le hP
  filter_upwards [hp, condDistrib_condition_observation μ X hX D hD] with x hx he
  rw [he]
  exact hx

end
end Nonsmooth
