import Nonsmooth.WeightedBayes
import Nonsmooth.SoftWeightLimits
import Nonsmooth.PosteriorKnownFunctions
import Nonsmooth.ConditionalEventBayes

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem absolutelyContinuous_map_measurable (μ ν : Measure β) (h : μ ≪ ν)
    (X : β → α) (hX : Measurable X) : μ.map X ≪ ν.map X := by
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hz
  rw [Measure.map_apply hX hS] at hz ⊢
  exact h hz

variable [StandardBorelSpace β] [Nonempty β]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual posterior means converge under bounded positive soft weights.
The countable family of Bayes identities is transferred to the target
observation law before applying dominated convergence within each posterior. -/
theorem soft_weighted_posterior_integral_tendsto (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (f : β → F) (hf : Integrable f μ)
    (w : ℕ → β → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n z, 0 ≤ w n z ∧ w n z ≤ 1) (hp : ∀ n, ∀ᵐ z ∂μ, 0 < w n z)
    (A : Set β) (hA : MeasurableSet A)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun n => w n z) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) z))) :
    ∀ᵐ x ∂μ[|A].map X,
      Tendsto (fun n => ∫ z, f z ∂condDistrib id X (weightedDensityLaw μ (w n)) x) atTop
        (𝓝 (∫ z, f z ∂condDistrib id X μ[|A] x)) := by
  let κ := condDistrib id X μ
  have hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ :=
    (compProd_map_condDistrib aemeasurable_id).symm
  have hbase : μ[|A].map X ≪ μ.map X :=
    absolutelyContinuous_map_measurable _ _ cond_absolutelyContinuous X hX
  have hpair : Integrable (fun p : α × β => f p.2) (μ.map (fun z => (X z, z))) :=
    hf.comp_snd_map_prodMk X
  have hki : ∀ᵐ x ∂μ.map X, Integrable f (κ x) := hpair.condDistrib_ae_map (Y := id) aemeasurable_id
  have hklim : ∀ᵐ x ∂μ.map X, ∀ᵐ z ∂κ x,
      Tendsto (fun n => w n z) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) z)) :=
    condDistrib_ae_inherits μ X hX hlim
  have hbayes (n : ℕ) : ∀ᵐ x ∂μ[|A].map X,
      condDistrib id X (weightedDensityLaw μ (w n)) x = weightedDensityLaw (κ x) (w n) := by
    have hAC : μ[|A] ≪ weightedDensityLaw μ (w n) := cond_absolutelyContinuous.trans
      (absolutelyContinuous_weightedDensityLaw μ (w n) (hw n)
        (unit_weight_integrable μ (w n) (hw n) (hb n)) (fun z => (hb n z).1) (hp n))
    have hmap := absolutelyContinuous_map_measurable _ _ hAC X hX
    filter_upwards [hmap.ae_le (weighted_law_posterior μ X hX κ hκ (w n) (hw n) (fun z => (hb n z).2))]
      with x hx
    exact hx.1
  filter_upwards [hbase.ae_le hki, hbase.ae_le hklim,
    event_conditioned_posterior μ X hX κ hκ A hA, ae_all_iff.mpr hbayes] with x hix hlx hAx hBx
  rw [hAx.1]
  have ht := soft_weighted_law_integral_tendsto (κ x) f hix w hw hb A hA hAx.2 hlx
  convert ht using 1
  funext n
  rw [hBx n]

end
end Nonsmooth
