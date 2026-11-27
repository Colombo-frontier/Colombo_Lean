import Nonsmooth.SelectionPosterior

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Joint observation and hidden-state kernel, allowing the observation to depend on the parameter. -/
def observedKernel (κ : Kernel α β) (F : α × β → γ) (_hF : Measurable F) : Kernel α (γ × β) :=
  (Kernel.id ×ₖ κ).map (fun p : α × β => (F p, p.2))

instance observedKernel_markov (κ : Kernel α β) [IsMarkovKernel κ]
    (F : α × β → γ) (hF : Measurable F) : IsMarkovKernel (observedKernel κ F hF) :=
  Kernel.IsMarkovKernel.map _ (hF.prodMk measurable_snd)

theorem observedKernel_apply (κ : Kernel α β) [IsMarkovKernel κ]
    (F : α × β → γ) (hF : Measurable F) (x : α) :
    observedKernel κ F hF x = (κ x).map (fun z : β => (F (x, z), z)) := by
  have hp : Measurable (fun p : α × β => (F p, p.2)) := hF.prodMk measurable_snd
  have hx : Measurable (fun z : β => (F (x, z), z)) :=
    (hF.comp measurable_prodMk_left).prodMk measurable_id
  ext S hS
  rw [observedKernel, Kernel.map_apply' _ hp _ hS, Kernel.id_prod_apply' _ _ (hp hS),
    Measure.map_apply hx hS]
  rfl

theorem observedKernel_fst (κ : Kernel α β) [IsMarkovKernel κ]
    (F : α × β → γ) (hF : Measurable F) (x : α) :
    (observedKernel κ F hF).fst x = (κ x).map (fun z => F (x, z)) := by
  have hx : Measurable (fun z : β => (F (x, z), z)) :=
    (hF.comp measurable_prodMk_left).prodMk measurable_id
  rw [Kernel.fst_apply, observedKernel_apply, Measure.map_map measurable_fst hx]
  rfl

variable [StandardBorelSpace β] [Nonempty β] [MeasurableSpace.CountablyGenerated γ]

def observedPosterior (κ : Kernel α β) [IsMarkovKernel κ]
    (F : α × β → γ) (hF : Measurable F) : Kernel (α × γ) β :=
  (observedKernel κ F hF).condKernel

instance observedPosterior_markov (κ : Kernel α β) [IsMarkovKernel κ]
    (F : α × β → γ) (hF : Measurable F) : IsMarkovKernel (observedPosterior κ F hF) := by
  unfold observedPosterior
  infer_instance

theorem observedPosterior_disintegrates (κ : Kernel α β) [IsMarkovKernel κ]
    (F : α × β → γ) (hF : Measurable F) (x : α) :
    (κ x).map (fun z : β => (F (x, z), z)) =
      ((κ x).map (fun z : β => F (x, z))) ⊗ₘ (Kernel.sectR (observedPosterior κ F hF) x) := by
  have h := congrArg (fun η : Kernel α (γ × β) => η x)
    (Kernel.disintegrate (observedKernel κ F hF) (observedKernel κ F hF).condKernel)
  try dsimp only at h
  rw [Kernel.compProd_apply_eq_compProd_sectR, observedKernel_apply, observedKernel_fst] at h
  exact h.symm

theorem observedPosterior_ae_eq_condDistrib (κ : Kernel α β) [IsMarkovKernel κ]
    (F : α × β → γ) (hF : Measurable F) (x : α) :
    ∀ᵐ y ∂(κ x).map (fun z : β => F (x, z)),
      observedPosterior κ F hF (x, y) = condDistrib id (fun z : β => F (x, z)) (κ x) y := by
  exact (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hF.comp measurable_prodMk_left) measurable_id
    (observedPosterior_disintegrates κ F hF x)).symm

/-- Disintegration commutes with mixing the parameter, retaining that parameter in the observation. -/
theorem kernel_disintegration_with_parameter (ν : Measure α) [SFinite ν]
    (κ : Kernel α (γ × β)) [IsMarkovKernel κ] :
    (ν ⊗ₘ κ).map (fun p : α × (γ × β) => ((p.1, p.2.1), p.2.2)) =
      (ν ⊗ₘ κ.fst) ⊗ₘ κ.condKernel := by
  have ha : Measurable (fun p : α × (γ × β) => ((p.1, p.2.1), p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  ext S hS
  rw [Measure.map_apply ha hS, Measure.compProd_apply (ha hS),
    Measure.compProd_apply hS,
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left hS)]
  apply lintegral_congr
  intro x
  have h := congrArg (fun η : Kernel α (γ × β) => η x)
    (Kernel.disintegrate κ κ.condKernel)
  try dsimp only at h
  rw [Kernel.compProd_apply_eq_compProd_sectR] at h
  rw [← h, Measure.compProd_apply (measurable_prodMk_left (ha hS))]
  rfl

end
end Nonsmooth
