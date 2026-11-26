import Nonsmooth.ObservedKernel

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β γ Ω : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace Ω]

theorem observedKernel_mix_map (ν : Measure α) [SFinite ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (F : α × β → γ) (hF : Measurable F) :
    ν ⊗ₘ observedKernel κ F hF =
      (ν ⊗ₘ κ).map (fun p : α × β => (p.1, (F p, p.2))) := by
  have hm : Measurable (fun p : α × β => (p.1, (F p, p.2))) :=
    measurable_fst.prodMk (hF.prodMk measurable_snd)
  ext S hS
  rw [Measure.compProd_apply hS, Measure.map_apply hm hS, Measure.compProd_apply (hm hS)]
  apply lintegral_congr
  intro x
  have hx : Measurable (fun z : β => (F (x, z), z)) :=
    (hF.comp measurable_prodMk_left).prodMk measurable_id
  rw [observedKernel_apply, Measure.map_apply hx (measurable_prodMk_left hS)]
  rfl

variable [StandardBorelSpace β] [Nonempty β] [MeasurableSpace.CountablyGenerated γ]

/-- Bayes updating of a regular conditional kernel by a parameter-dependent new observation. -/
theorem observedPosterior_update_joint (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (hX : Measurable X) (Y : Ω → β) (hY : Measurable Y)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : (μ.map X) ⊗ₘ κ = μ.map (fun a => (X a, Y a)))
    (F : α × β → γ) (hF : Measurable F) :
    μ.map (fun a => ((X a, F (X a, Y a)), Y a)) =
      (μ.map (fun a => (X a, F (X a, Y a)))) ⊗ₘ observedPosterior κ F hF := by
  let ξ := observedKernel κ F hF
  have hp : Measurable (fun a : Ω => (X a, Y a)) := hX.prodMk hY
  have hm : Measurable (fun p : α × β => (p.1, (F p, p.2))) :=
    measurable_fst.prodMk (hF.prodMk measurable_snd)
  have ha : Measurable (fun p : α × (γ × β) => ((p.1, p.2.1), p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hmix : (μ.map X) ⊗ₘ ξ = μ.map (fun a => (X a, (F (X a, Y a), Y a))) := by
    rw [observedKernel_mix_map, hκ, Measure.map_map hm hp]
    rfl
  have htrip : μ.map (fun a => ((X a, F (X a, Y a)), Y a)) =
      ((μ.map X) ⊗ₘ ξ.fst) ⊗ₘ observedPosterior κ F hF := by
    have h := kernel_disintegration_with_parameter (μ.map X) ξ
    have ht : Measurable (fun a : Ω => (X a, (F (X a, Y a), Y a))) :=
      hX.prodMk ((hF.comp hp).prodMk hY)
    rw [hmix, Measure.map_map ha ht] at h
    exact h
  have hbase := congrArg Measure.fst htrip
  rw [Measure.fst_map_prodMk hY, Measure.fst_compProd] at hbase
  rw [← hbase] at htrip
  exact htrip

theorem observedPosterior_update_base (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (hX : Measurable X) (Y : Ω → β) (hY : Measurable Y)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : (μ.map X) ⊗ₘ κ = μ.map (fun a => (X a, Y a)))
    (F : α × β → γ) (hF : Measurable F) :
    μ.map (fun a => (X a, F (X a, Y a))) =
      (μ.map X) ⊗ₘ (observedKernel κ F hF).fst := by
  have hp : Measurable (fun a : Ω => (X a, Y a)) := hX.prodMk hY
  have hm : Measurable (fun p : α × β => (p.1, (F p, p.2))) :=
    measurable_fst.prodMk (hF.prodMk measurable_snd)
  have ha : Measurable (fun p : α × (γ × β) => ((p.1, p.2.1), p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have h := kernel_disintegration_with_parameter (μ.map X) (observedKernel κ F hF)
  rw [observedKernel_mix_map, hκ, Measure.map_map hm hp,
    Measure.map_map ha (hm.comp hp)] at h
  dsimp only [Function.comp_def] at h
  have hb := congrArg Measure.fst h
  rw [Measure.fst_map_prodMk hY, Measure.fst_compProd] at hb
  exact hb

theorem observedPosterior_update_ae_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (hX : Measurable X) (Y : Ω → β) (hY : Measurable Y)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : (μ.map X) ⊗ₘ κ = μ.map (fun a => (X a, Y a)))
    (F : α × β → γ) (hF : Measurable F) :
    ∀ᵐ p ∂μ.map (fun a => (X a, F (X a, Y a))), observedPosterior κ F hF p =
      condDistrib Y (fun a => (X a, F (X a, Y a))) μ p :=
  (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hX.prodMk (hF.comp (hX.prodMk hY))) hY
    (observedPosterior_update_joint μ X hX Y hY κ hκ F hF)).symm

end
end Nonsmooth
