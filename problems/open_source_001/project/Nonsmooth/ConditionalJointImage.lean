import Nonsmooth.ConditionalImage

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]

theorem condDistrib_joint_image (μ : Measure α) [IsFiniteMeasure μ]
    (X : α → β) (Y : α → γ) :
    condDistrib Prod.snd Prod.fst (μ.map (fun a => (X a, Y a))) = condDistrib Y X μ := by
  rw [condDistrib, condDistrib]
  change ((μ.map (fun a => (X a, Y a))).map id).condKernel = _
  simp only [Measure.map_id]

variable [StandardBorelSpace α] [Nonempty α]

theorem condDistrib_hidden_image_ae (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → β) (hX : Measurable X) (Y : α → γ) (hY : Measurable Y) :
    ∀ᵐ x ∂μ.map X, condDistrib Y X μ x = (condDistrib id X μ x).map Y := by
  let κ := (condDistrib id X μ).map Y
  letI : IsMarkovKernel κ := Kernel.IsMarkovKernel.map _ hY
  have hj : μ.map (fun a => (X a, Y a)) = (μ.map X) ⊗ₘ κ :=
    condDistrib_image_disintegration μ X hX Y hY
  have he := (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX hY hj).symm
  filter_upwards [he] with x hx
  rw [← hx]
  exact Kernel.map_apply _ hY _

end
end Nonsmooth
