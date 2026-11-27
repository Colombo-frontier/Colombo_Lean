import Nonsmooth.ObservedKernel

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {k : ℕ}

def rowMarginalKernel (κ : Kernel α (Fin k → β)) (i : Fin k) : Kernel α β :=
  κ.map (fun a => a i)

instance rowMarginalKernel_markov (κ : Kernel α (Fin k → β)) [IsMarkovKernel κ] (i : Fin k) :
    IsMarkovKernel (rowMarginalKernel κ i) :=
  Kernel.IsMarkovKernel.map κ (measurable_pi_apply i)

def productMarginalKernel (κ : Kernel α (Fin k → β)) [IsMarkovKernel κ] : Kernel α (Fin k → β) :=
  finiteProductKernel (rowMarginalKernel κ)

instance productMarginalKernel_markov (κ : Kernel α (Fin k → β)) [IsMarkovKernel κ] :
    IsMarkovKernel (productMarginalKernel κ) := by
  unfold productMarginalKernel
  infer_instance

theorem rowMarginalKernel_apply (κ : Kernel α (Fin k → β)) (i : Fin k) (x : α) :
    rowMarginalKernel κ i x = (κ x).map (fun a => a i) :=
  Kernel.map_apply κ (measurable_pi_apply i) x

theorem productMarginalKernel_apply (κ : Kernel α (Fin k → β)) [IsMarkovKernel κ] (x : α) :
    productMarginalKernel κ x = Measure.pi (fun i => (κ x).map (fun a => a i)) := by
  change Measure.pi (fun i => rowMarginalKernel κ i x) = _
  simp only [rowMarginalKernel_apply]

theorem productMarginalKernel_independent (κ : Kernel α (Fin k → β)) [IsMarkovKernel κ] (x : α) :
    iIndepFun (fun i (a : Fin k → β) => a i) (productMarginalKernel κ x) :=
  finiteProductKernel_independent _ _

theorem independent_iff_productMarginalKernel (κ : Kernel α (Fin k → β)) [IsMarkovKernel κ] (x : α) :
    iIndepFun (fun i (a : Fin k → β) => a i) (κ x) ↔ κ x = productMarginalKernel κ x := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable),
    productMarginalKernel_apply]
  change (κ x).map id = _ ↔ _
  rw [Measure.map_id]

theorem kernel_ae_eq_of_ae_ae {γ : Type} [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α β) [IsMarkovKernel κ]
    (η θ : Kernel (α × β) γ) [IsMarkovKernel η] [IsMarkovKernel θ]
    (h : ∀ᵐ x ∂ν, ∀ᵐ y ∂κ x, η (x, y) = θ (x, y)) :
    η =ᵐ[ν ⊗ₘ κ] θ := by
  have he : (ν ⊗ₘ κ) ⊗ₘ η = (ν ⊗ₘ κ) ⊗ₘ θ := by
    ext S hS
    rw [Measure.compProd_apply hS, Measure.compProd_apply hS,
      Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left (κ := η) hS),
      Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left (κ := θ) hS)]
    apply lintegral_congr_ae
    filter_upwards [h] with x hx
    apply lintegral_congr_ae
    filter_upwards [hx] with y hy
    rw [hy]
  have hη := eq_condKernel_of_measure_eq_compProd η
    (ρ := (ν ⊗ₘ κ) ⊗ₘ η) (by rw [Measure.fst_compProd])
  have hθ := eq_condKernel_of_measure_eq_compProd θ
    (ρ := (ν ⊗ₘ κ) ⊗ₘ η) (by rw [Measure.fst_compProd]; exact he)
  rw [Measure.fst_compProd] at hη hθ
  filter_upwards [hη, hθ] with x hxη hxθ
  exact hxη.trans hxθ.symm

end
end Nonsmooth
