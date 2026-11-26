import Mathlib.Probability.Kernel.CondDistrib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Task006.ConditionalKernelComposition

noncomputable section
variable {α H V V' : Type*} [MeasurableSpace α] [MeasurableSpace H]
  [MeasurableSpace V] [MeasurableSpace V']

abbrev dependentMap (κ : Kernel H V) (f : H × V → V') : Kernel H V' :=
  (Kernel.id ×ₖ κ).map f

theorem dependentMap_apply (κ : Kernel H V) [IsSFiniteKernel κ]
    (f : H × V → V') (hf : Measurable f) (h : H) :
    dependentMap κ f h = (κ h).map (fun v => f (h,v)) := by
  have hfa : Measurable (fun v : V => f (h,v)) := hf.comp measurable_prodMk_left
  ext s hs
  rw [dependentMap,Kernel.map_apply' _ hf h hs,
    Kernel.id_prod_apply' κ h (hf hs),Measure.map_apply hfa hs]
  rfl

theorem compProd_dependentMap (ν : Measure H) [SFinite ν]
    (κ : Kernel H V) [IsSFiniteKernel κ] (f : H × V → V') (hf : Measurable f) :
    ν ⊗ₘ dependentMap κ f = (ν ⊗ₘ κ).map (fun p => (p.1,f p)) := by
  ext s hs
  have hT : Measurable (fun p : H × V => (p.1,f p)) := measurable_fst.prodMk hf
  rw [Measure.compProd_apply hs,Measure.map_apply hT hs,Measure.compProd_apply (hT hs)]
  apply lintegral_congr
  intro h
  have hfa : Measurable (fun v : V => f (h,v)) := hf.comp measurable_prodMk_left
  rw [dependentMap_apply κ f hf h,
    Measure.map_apply hfa (measurable_prodMk_left hs)]
  rfl

/-- Conditional pushforward by a map that depends on the observed history.
The kernel formula is proved from the real joint law and disintegration
uniqueness, rather than introduced as a conditional-distribution assumption. -/
theorem condDistrib_dependent_comp [StandardBorelSpace V] [Nonempty V]
    [StandardBorelSpace V'] [Nonempty V']
    (μ : Measure α) [IsFiniteMeasure μ]
    (obs : α → H) (hobs : Measurable obs) (Y : α → V) (hY : Measurable Y)
    (f : H × V → V') (hf : Measurable f) :
    condDistrib (fun ω => f (obs ω,Y ω)) obs μ =ᵐ[μ.map obs]
      dependentMap (condDistrib Y obs μ) f := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hobs
    (hf.comp (hobs.prodMk hY))
  have hT : Measurable (fun p : H × V => (p.1,f p)) := measurable_fst.prodMk hf
  calc
    μ.map (fun ω => (obs ω,f (obs ω,Y ω))) =
        (μ.map (fun ω => (obs ω,Y ω))).map (fun p => (p.1,f p)) := by
      rw [Measure.map_map hT (hobs.prodMk hY)]
      rfl
    _ = ((μ.map obs) ⊗ₘ condDistrib Y obs μ).map (fun p => (p.1,f p)) := by
      rw [compProd_map_condDistrib hY.aemeasurable]
    _ = _ := (compProd_dependentMap (μ.map obs) (condDistrib Y obs μ) f hf).symm

#print axioms condDistrib_dependent_comp

end
end Task006.ConditionalKernelComposition
